//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------

#include "Answer.hpp"

#include <algorithm>
#include <cfloat>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <limits>
#include <numeric>
#include <random>
#include <set>
#include <unordered_map>
#include <vector>

using namespace std;

#ifdef LOCAL

#define ASSERT(x, msg)\
assert(x && msg);

#define ADD_INT(n, a)\
n += a;

#define ASSIGN_INT(n, a)\
n = a;

#define OUTPUT_TO_ERR(x)\
cerr << x << endl;

#define OUTPUT_STAGE_COUNT(stage_count)\
OUTPUT_TO_ERR(stage_count);

#define OUTPUT_TURN_COUNT(turn_count)\
//OUTPUT_TO_ERR(turn_count);

#define PRINT_PUT_COOKIE(turn, width, height, position, oven) \
/*cerr << "-----------クッキーを置きました。-----------" << endl; \
cerr << "Turn: " << stage.turn() << endl; \
cerr << "Width: " << width << endl; \
cerr << "Height: " << height << endl; \
cerr << "Position: " << "(" << position.x << ", " << position.y << ")" << endl; \
oven.Print() \*/

#define ADD_PUT_COUNT(lane_type, small_put_count, large_put_count)\
if (lane_type == CandidateLaneType_Small) { \
    ++small_put_count; \
}else { \
    ++large_put_count; \
}

#define OUTPUT_PUT_COUNT(msg, put_count)\
cerr << msg; \
OUTPUT_TO_ERR(put_count);

#define CHECK_INTERSECT(stage_count, stage, width, height, position, oven_state)\
if (!stage.oven().isAbleToPut(width, height, position)) { \
    cerr << "-----------クッキーが衝突しています。-----------" << endl; \
    cerr << "Stage: " << stage_count << endl; \
    cerr << "Turn: " << stage.turn() << endl; \
    cerr << "Width: " << width << endl; \
    cerr << "Height: " << height << endl; \
    cerr << "Position: " << "(" << position.x << ", " << position.y << ")" << endl; \
    oven_state.Print(); \
    assert(false); \
}

#define CHECK_CELL_EMPTY(width, height, x, y, oven, state, cell_empty) \
if (state != cell_empty) { \
    cerr << "Width: " << width << endl; \
    cerr << "Height: " << height << endl; \
    cerr << "Position: " << "(" << x << ", " << y << ")" << endl; \
    oven->Print(); \
    assert(false); \
}

#else
#define ASSERT(x)
#define ADD_INT(n, a)
#define ASSIGN_INT(n, a)
#define OUTPUT_TO_ERR(x)
#define OUTPUT_STAGE_COUNT(stage_count)
#define OUTPUT_TURN_COUNT(turn_count)
#define PRINT_PUT_COOKIE(turn, width, height, position, oven)
#define ADD_PUT_COUNT(lane_type, small_put_count, large_put_count)
#define OUTPUT_PUT_COUNT(msg, put_count)
#define CHECK_INTERSECT(stage_count, stage, width, height, position, oven_state)
#define CHECK_CELL_EMPTY(width, height, x, y, oven, state, cell_empty)
#endif

//------------------------------------------------------------------------------
namespace hpc {

	template<class T>
	T Min(T v1, T v2) {
		return (v1 < v2) ? v1 : v2;
	}
	template<class T>
	T Max(T v1, T v2) {
		return (v1 < v2) ? v2 : v1;
	}

	template<int32_t x, int32_t n>
	struct Power final {
		static constexpr int32_t value = x * Power<x, n - 1>::value;
	};
	template<int32_t x>
	struct Power<x, 0> final {
		static constexpr int32_t value = 1;
	};

	template<class T>
	void UnstableFastErase(int32_t index, T& container) {
		swap(container[index], container.back());
		container.pop_back();
	}

	template<class T, class U>
	void LinearUnstableFastErase(const T& value, U& container) {
		const auto itr = find(container.begin(), container.end(), value);
		if (itr == container.end()) {
			return;
		}
		UnstableFastErase(distance(container.begin(), itr), container);
	}

	template<class T, class U>
	const typename T::value_type& RandomChoise(const T& container, U& random_engine) {
		return container[random_engine.rand() % container.size()];
	}

	template<class T, class U>
	const typename T::value_type& RandomChoise(const T& container, U& random_engine, int32_t size) {
		return container[random_engine.rand() % Min(static_cast<int32_t>(container.size()), size)];
	}


	constexpr int32_t g_invalid_int = -1;
	constexpr int32_t g_cell_empty = 0;
	constexpr int32_t g_cell_fill = 1;
	constexpr int32_t g_table_row_count = (Parameter::OvenWidth + 2);
	constexpr int32_t g_table_column_count = (Parameter::OvenHeight + 2);

	constexpr int32_t g_max_piece_index = (Parameter::CandidatePieceCount - 1);

	constexpr int32_t g_reserve_large_count = 2;

	constexpr CandidateLaneType g_lane_types[] = { CandidateLaneType_Small, CandidateLaneType_Large };

	constexpr float g_inf = FLT_MAX;
	constexpr float g_half_inf = FLT_MAX * 0.5f;

	constexpr double g_game_time_limit = 60.0f;
	constexpr double g_stage_time_limit = g_game_time_limit / (static_cast<double>(Parameter::GameStageCount));
	constexpr double g_turn_time_limit = (g_stage_time_limit / static_cast<double>(Parameter::GameTurnLimit));



	bool IsGameOver(int32_t current_turn, int32_t required_heat_turn_count) {
		const int32_t rest_turn_count = (Parameter::GameTurnLimit - current_turn);
		if (rest_turn_count <= required_heat_turn_count) {
			return true;
		}
		return false;
	}
	bool IsGameOver(int32_t current_turn, const Piece& piece) {
		return IsGameOver(current_turn, piece.requiredHeatTurnCount());
	}
	bool IsGameOver(int32_t current_turn, const CandidatePieces& pieces) {
		const int32_t rest_heat_turn = (Parameter::GameTurnLimit - current_turn - 1);
		for (const Piece& piece : pieces) {
			if (rest_heat_turn < piece.requiredHeatTurnCount()) {
				continue;
			}
			return false;
		}
		return true;
	}

	int32_t OvenRight(int32_t x, int32_t width) {
		return (x + width - 1);
	}
	int32_t OvenBottom(int32_t y, int32_t height) {
		return (y + height - 1);
	}

	int32_t MinAreaArg(const vector<int32_t>& piece_indices, const CandidatePieces& pieces) {
		int32_t min_area_arg = 0;
		float min_area = static_cast<float>(Parameter::OvenWidth * Parameter::OvenHeight);
		for (int32_t piece_index : piece_indices) {
			const Piece& piece = pieces[piece_index];
			const float area = static_cast<float>(piece.width(), piece.height());
			if (min_area <= area) {
				continue;
			}
			min_area_arg = piece_index;
			min_area = area;
		}
		return min_area_arg;
	}
	int32_t MinAreaArg(const CandidatePieces& pieces) {
		int32_t min_area_arg = 0;
		float min_area = static_cast<float>(Parameter::OvenWidth * Parameter::OvenHeight);
		for (int32_t piece_index = 0; piece_index < pieces.count(); ++piece_index) {
			const Piece& piece = pieces[piece_index];
			const float area = static_cast<float>(piece.width(), piece.height());
			if (min_area <= area) {
				continue;
			}
			min_area_arg = piece_index;
			min_area = area;
		}
		return min_area_arg;
	}

	bool IsInAreaX(int32_t oven_x, int32_t width) {
		const int32_t right = OvenRight(oven_x, width);
		return (0 <= oven_x) && (right < Parameter::OvenWidth);
	}
	bool IsInAreaY(int32_t oven_y, int32_t height) {
		const int32_t bottom = OvenBottom(oven_y, height);
		return (0 <= oven_y) && (bottom < Parameter::OvenHeight);
	}
	bool IsInArea(int32_t oven_x, int32_t oven_y, int32_t width, int32_t height) {
		return IsInAreaX(oven_x, width) && IsInAreaY(oven_y, height);
	}
	bool IsInArea(int32_t oven_x, int32_t oven_y) {
		return (0 <= oven_x) && (oven_x < Parameter::OvenWidth) && (0 <= oven_y) && (oven_y < Parameter::OvenHeight);
	}




	class Tmr final {
		chrono::high_resolution_clock::time_point start, end;
		double limit;

	public:
		Tmr() {
			start = chrono::high_resolution_clock::now();
		}
		Tmr(double l) {
			start = chrono::high_resolution_clock::now();
			limit = l;
		}

		double getTime() {
			end = chrono::high_resolution_clock::now();
			return chrono::duration<double>(end - start).count();
		}

		bool isTimeOver() {
			if (getTime() > limit) {
				return true;
			}
			return false;
		}

		double getLimit() { return limit; }
		void setLimit(double l) {
			limit = l;
		}
		void setStart() { start = chrono::high_resolution_clock::now(); }
	};

	Tmr g_timer;



	class Xor128 final {
		unsigned static int x, y, z, w;
	public:
		Xor128() {
			x = 31103110, y = 123456789, z = 521288629, w = 88675123;
		}

		unsigned int rand()
		{
			unsigned int t;
			t = (x ^ (x << 11)); x = y; y = z; z = w;
			return(w = (w ^ (w >> 19)) ^ (t ^ (t >> 8)));
		}
	};
	unsigned int Xor128::x, Xor128::y, Xor128::z, Xor128::w;

	Xor128 g_xor128;


	struct Edge final {
		Edge() = default;
		Edge(Vector2i&& s, Vector2i&& e)
			:
			start(move(s)),
			end(move(e))
		{
			;
		}
		Edge(const Vector2i& s, const Vector2i& e)
			:
			start(s),
			end(e)
		{
			;
		}
		Vector2i start = Vector2i::Zero();
		Vector2i end = Vector2i::Zero();
	};



	struct PutInfo final {

		static PutInfo Invalid() {
			PutInfo put_info;
			put_info.is_valid = false;
			put_info.evaluation = -g_half_inf;
			return put_info;
		}

		PutInfo() = default;

		PutInfo(
			float e,
			int32_t pi,
			int32_t w,
			int32_t h,
			int32_t r,
			CandidateLaneType lt,
			int32_t pt,
			const Vector2i& p
		)
			:
			is_valid(true),
			evaluation(e),
			piece_index(pi),
			width(w),
			height(h),
			rhtc(r),
			lane_type(lt),
			put_turn(pt),
			position(p)
		{
			;
		}

		bool IsIntersect(const PutInfo& rhs) const {
			return Util::IsIntersect(
				position,
				width,
				height,
				rhs.position,
				rhs.width,
				rhs.height
			);
		}

		bool IsAbleToBake(int32_t turn, const PutInfo& rhs) const {
			const int32_t heat_turn = (rhs.put_turn - turn - 1);
			if (rhtc <= heat_turn) {
				return true;
			}
			return false;
		}

		bool IsBaked(int32_t turn) const {
			const int32_t heat_turn = (turn - put_turn);
			if (rhtc < heat_turn) {
				return true;
			}
			return false;
		}

		bool IsAbleToPut(int32_t turn, const PutInfo& rhs) const {
			return IsAbleToBake(turn, rhs) || !IsIntersect(rhs);
		}

		operator bool() const {
			return is_valid;
		}

		bool operator>(const PutInfo& rhs) const {
			return evaluation > rhs.evaluation;
		}

		bool is_valid = false;
		float evaluation = -g_half_inf;
		int32_t piece_index = 0;
		int32_t width = 0;
		int32_t height = 0;
		int32_t rhtc = 0;
		CandidateLaneType lane_type = CandidateLaneType_Large;
		int32_t put_turn = 0;
		Vector2i position = Vector2i::Zero();
	};


	struct BakingPiece final {
		BakingPiece() = default;
		BakingPiece(int32_t w, int32_t h, int32_t rhtc, const Vector2i& p)
			:
			width(w),
			height(h),
			rrhtc(rhtc),
			position(p)
		{
			;
		}
		int32_t width = 0;
		int32_t height = 0;
		int32_t rrhtc = 0;
		Vector2i position = Vector2i::Zero();
	};


	class Smoother final {

	public:

		void Initialize() {
			sum = 0;
			min_value = numeric_limits<int32_t>::max();
			max_value = 0;
			count = 0;
		}

		void Add(int32_t value) {
			sum += value;
			min_value = Min(min_value, value);
			max_value = Max(max_value, value);
			++count;
		}

		int32_t GetMaxValue() const {
			return max_value;
		}

		int32_t GetMinValue() const {
			return min_value;
		}

		float GetMean() const {
			return (static_cast<float>(sum) / static_cast<float>(count));
		}

		float GetProportion(int32_t value) const {
			return (static_cast<float>(value - min_value) / static_cast<float>(max_value - min_value));
		}

	private:

		int32_t sum = 0;
		int32_t min_value = 0;
		int32_t max_value = 0;
		int32_t count = 0;
	};


	class OvenState final {

	public:

		OvenState() {
			state_.resize(g_table_column_count);
			for (int32_t column_index = 0; column_index < g_table_column_count; ++column_index) {
				state_[column_index].resize(g_table_row_count, g_cell_empty);
			}
		}

		void Initialize() {
			for (int32_t column_index = 0; column_index < g_table_column_count; ++column_index) {
				const bool top_row_or_bottom_row = (column_index == 0 || column_index == (g_table_column_count - 1));
				if (top_row_or_bottom_row) {
					fill(state_[column_index].begin(), state_[column_index].end(), g_cell_fill);
				}
				else {
					fill(state_[column_index].begin(), state_[column_index].end(), g_cell_empty);
					state_[column_index][0] = state_[column_index][g_table_row_count - 1] = g_cell_fill;
				}
			}
			baking_pieces_.clear();
		}

		void Print() const {
			for (int32_t row_index = 0; row_index < g_table_row_count; ++row_index) {
				for (int32_t column_index = 0; column_index < g_table_column_count; ++column_index) {
					cerr << state_[row_index][column_index];
				}
				cerr << endl;
			}
			cerr << endl;
		}

		void PutPiece(int32_t width, int32_t height, int32_t rhtc, const Vector2i& position) {
			PutPiece(width, height, rhtc, position.x, position.y);
		}
		void PutPiece(const Piece& piece, const Vector2i& position) {
			PutPiece(piece.width(), piece.height(), piece.requiredHeatTurnCount(), position);
		}
		void PutPiece(const PutInfo& put_info) {
			PutPiece(put_info.width, put_info.height, put_info.rhtc, put_info.position);
		}
		void PutPiece(int32_t width, int32_t height, int32_t rhtc, int32_t x, int32_t y) {
			ChangeState(g_cell_fill, width, height, x, y);
			baking_pieces_.emplace_back(width, height, rhtc, Vector2i(x, y));
		}

		void ChangeState(int32_t state, int32_t width, int32_t height, const Vector2i& position) {
			ChangeState(state, width, height, position.x, position.y);
		}
		void ChangeState(int32_t state, int32_t width, int32_t height, int32_t oven_x, int32_t oven_y) {
			const int32_t left = oven_x;
			const int32_t right = OvenRight(left, width);
			const int32_t top = oven_y;
			const int32_t bottom = OvenBottom(top, height);
			for (int32_t x = left; x <= right; ++x) {
				for (int32_t y = top; y <= bottom; ++y) {
					state_[y + 1][x + 1] = state;
				}
			}
		}


		bool Update() {
			bool removed = false;
			for (int32_t bp_index = 0; bp_index < static_cast<int32_t>(baking_pieces_.size()); ++bp_index) {
				BakingPiece& bp = baking_pieces_[bp_index];
				int32_t& rrhtc = bp.rrhtc;
				--rrhtc;
				constexpr int32_t baked = -1;
				if (rrhtc != baked) {
					continue;
				}
				removed = true;
				ChangeState(g_cell_empty, bp.width, bp.height, bp.position);
				UnstableFastErase(bp_index, baking_pieces_);
				--bp_index;
			}
			return removed;
		}

		bool IsIntersect(int32_t width, int32_t height, int32_t oven_x, int32_t oven_y) const {
			const int32_t left = oven_x;
			const int32_t right = OvenRight(left, width);
			const int32_t top = oven_y;
			const int32_t bottom = OvenBottom(top, height);
			for (int32_t x = left; x <= right; ++x) {
				for (int32_t y = top; y <= bottom; ++y) {
					const int32_t bit = state_[y + 1][x + 1];
					if (bit == g_cell_fill) {
						return true;
					}
				}
			}
			return false;
		}
		bool IsIntersect(int32_t width, int32_t height, const Vector2i& position) const {
			return IsIntersect(width, height, position.x, position.y);
		}

		bool IsAbleToPut(int32_t width, int32_t height, int32_t x, int32_t y) const {
			const bool is_in_area = IsInArea(x, y, width, height);
			if (!is_in_area) {
				return false;
			}
			return !IsIntersect(width, height, x, y);
		}
		bool IsAbleToPut(int32_t width, int32_t height, const Vector2i& position) const {
			return IsAbleToPut(width, height, position.x, position.y);
		}


		float GetLiberty(int32_t width, int32_t height, const Vector2i& oven_left_top) const {
			return GetLiberty(width, height, oven_left_top.x, oven_left_top.y);
		}
		float GetLiberty(int32_t width, int32_t height, int32_t oven_left, int32_t oven_top) const {
			const int32_t oven_right = OvenRight(oven_left, width);
			const int32_t oven_bottom = OvenBottom(oven_top, height);
			const Edge left_edge(Vector2i(oven_left - 1, oven_top), Vector2i(oven_left - 1, oven_bottom));
			const Edge top_edge(Vector2i(oven_left, oven_top - 1), Vector2i(oven_right, oven_top - 1));
			const Edge right_edge(Vector2i(oven_right + 1, oven_top), Vector2i(oven_right + 1, oven_bottom));
			const Edge bottom_edge(Vector2i(oven_left, oven_bottom + 1), Vector2i(oven_right, oven_bottom + 1));
			const int32_t length = (width + height) * 2;
			int32_t liberty = 0;
			liberty += GetLiberty(left_edge);
			liberty += GetLiberty(top_edge);
			liberty += GetLiberty(right_edge);
			liberty += GetLiberty(bottom_edge);
			return static_cast<float>(liberty) / static_cast<float>(length);
		}

		int32_t GetCellCount() {
			int32_t cell_count = 0;
			for (int32_t row_index = 1; row_index < (g_table_row_count - 1); ++row_index) {
				for (int32_t column_index = 1; column_index < (g_table_column_count - 1); ++column_index) {
					cell_count += state_[row_index][column_index];
				}
			}
			return cell_count;
		}


	private:

		int32_t GetLiberty(const Edge& edge) const {
			const int32_t table_left = (edge.start.x + 1);
			const int32_t table_top = (edge.start.y + 1);
			const int32_t table_right = (edge.end.x + 1);
			const int32_t table_bottom = (edge.end.y + 1);
			int32_t liberty = 0;
			for (int32_t table_x = table_left; table_x <= table_right; ++table_x) {
				for (int32_t table_y = table_top; table_y <= table_bottom; ++table_y) {
					liberty += state_[table_y][table_x];
				}
			}
			return liberty;
		}


		vector<vector<int32_t>> state_;
		vector<BakingPiece> baking_pieces_;

	};



	vector<PutInfo> g_put_infos_1;
	vector<PutInfo> g_put_infos_2;
	vector<PutInfo> g_put_infos_3;
	vector<PutInfo> g_put_infos_4;
	//vector<vector<PutInfo>> g_put_infos_5;


	Smoother g_rhtc_smoother[CandidateLaneType_TERM];




	float EvaluatePiece(CandidateLaneType lane_type, const Piece& piece) {
		constexpr float area_weight = 0.01f;
		const float bias = (lane_type == CandidateLaneType_Small) ? 0.0f : 1.0f;
		const float area = static_cast<float>(piece.width() * piece.height());
		const float f_rhtc = static_cast<float>(piece.requiredHeatTurnCount());
		return (bias + (1.0f / (area * area_weight + f_rhtc)));
	}


	float EvaluatePosition(
		int32_t width,
		int32_t height,
		int32_t rhtc,
		int32_t score,
		int32_t x,
		int32_t y,
		CandidateLaneType lane_type,
		const OvenState& oven
	) {

		float liberty = 0.0f;

		OvenState oven_clone = oven;
		for (int32_t ht_index = 0; ht_index < rhtc; ++ht_index) {
			oven_clone.Update();
			liberty += oven_clone.GetLiberty(width, height, x, y);
		}
		liberty /= static_cast<float>(rhtc);

		return liberty;
	}


	PutInfo GetBestPutInfo(
		int32_t turn,
		int32_t piece_index,
		CandidateLaneType lane_type,
		const Piece& piece,
		const OvenState& oven
	) {

		if (IsGameOver(turn, piece)) {
			return PutInfo::Invalid();
		}

		PutInfo put_info = PutInfo::Invalid();

		const int32_t width = piece.width();
		const int32_t height = piece.height();
		const int32_t rhtc = piece.requiredHeatTurnCount();
		const int32_t score = piece.score();

		put_info.piece_index = piece_index;
		put_info.width = width;
		put_info.height = height;
		put_info.rhtc = rhtc;
		put_info.lane_type = lane_type;
		put_info.put_turn = turn;

		for (int32_t x = 0; x < Parameter::OvenWidth; ++x) {
			const bool is_in_area_x = IsInAreaX(x, width);
			if (!is_in_area_x) {
				break;
			}
			for (int32_t y = 0; y < Parameter::OvenHeight; ++y) {
				const bool is_in_area_y = IsInAreaY(y, height);
				if (!is_in_area_y) {
					break;
				}
				if (!oven.IsAbleToPut(width, height, x, y)) {
					continue;
				}
				const float evaluation = EvaluatePosition(width, height, rhtc, score, x, y, lane_type, oven);
				if (evaluation <= put_info.evaluation) {
					continue;
				}
				put_info.is_valid = true;
				put_info.evaluation = evaluation;
				put_info.position.x = x;
				put_info.position.y = y;
			}
		}

		return put_info;
	}

	vector<PutInfo> GetPutableInfos(
		int32_t turn,
		int32_t piece_index,
		CandidateLaneType lane_type,
		const Piece& piece,
		const OvenState& oven
	) {

		if (IsGameOver(turn, piece)) {
			return vector<PutInfo>();
		}

		g_put_infos_4.clear();

		const int32_t width = piece.width();
		const int32_t height = piece.height();
		const int32_t rhtc = piece.requiredHeatTurnCount();
		const int32_t score = piece.score();

		for (int32_t x = 0; x < Parameter::OvenWidth; ++x) {
			const bool is_in_area_x = IsInAreaX(x, width);
			if (!is_in_area_x) {
				break;
			}
			for (int32_t y = 0; y < Parameter::OvenHeight; ++y) {
				const bool is_in_area_y = IsInAreaY(y, height);
				if (!is_in_area_y) {
					break;
				}
				if (!oven.IsAbleToPut(width, height, x, y)) {
					continue;
				}
				const float evaluation = EvaluatePosition(width, height, rhtc, score, x, y, lane_type, oven);
				if (evaluation < -g_half_inf) {
					continue;
				}
				g_put_infos_4.emplace_back(
					evaluation,
					piece_index,
					width,
					height,
					rhtc,
					lane_type,
					turn,
					Vector2i(x, y)
				);
			}
		}

		return g_put_infos_4;
	}




	int32_t g_stage_count = 0;
	int32_t g_large_put_count = 0;
	int32_t g_total_put_large_count = 0;
	int32_t g_small_put_count = 0;
	int32_t g_total_put_small_count = 0;


	const Stage* g_stage = nullptr;

	CandidateLaneType g_pre_put_lane_type = CandidateLaneType_TERM;

	OvenState g_oven;

	int32_t g_best_turn = Parameter::GameTurnLimit;
	vector<PutInfo> g_reserved_larges;


	int32_t RestTurnCount() {
		return (Parameter::GameTurnLimit - g_stage->turn());
	}

	void ReserveLarges() {

		int32_t turn = g_stage->turn();

		const CandidatePieces& large_pieces = g_stage->candidateLane(CandidateLaneType_Large).pieces();

		g_put_infos_1.clear();
		for (int32_t piece_index = 0; piece_index < Parameter::CandidatePieceCount; ++piece_index) {
			const Piece& piece = large_pieces[piece_index];
			vector<PutInfo> pi = GetPutableInfos(turn, piece_index, CandidateLaneType_Large, piece, g_oven);
			if (pi.empty()) {
				continue;
			}
			move(pi.begin(), pi.end(), back_inserter(g_put_infos_1));
		}

		if (g_put_infos_1.empty()) {
			return;
		}

		sort(g_put_infos_1.begin(), g_put_infos_1.end(), greater<PutInfo>());

		if (g_reserved_larges.empty()) {
			g_best_turn = Parameter::GameTurnLimit;
		}

		bool success = false;
		constexpr int32_t loop_max = 3;
		int32_t loop = 0;
		for (const PutInfo& pi : g_put_infos_1) {

			if (loop == loop_max) {
				break;
			}
			++loop;

			int32_t simulation_turn = turn;
			int32_t first_piece_index = pi.piece_index;
			vector<int32_t> rest_indices(Parameter::CandidatePieceCount);
			iota(rest_indices.begin(), rest_indices.end(), 0);
			UnstableFastErase(first_piece_index, rest_indices);
			vector<PutInfo> history;
			history.reserve(Parameter::CandidatePieceCount);
			history.push_back(pi);
			OvenState oven_clone = g_oven;
			oven_clone.PutPiece(pi);

			const auto is_continue = [&simulation_turn, &rest_indices]() {
				const int32_t rest_count = static_cast<int32_t>(g_reserved_larges.size());
				const int32_t put_count = Parameter::CandidatePieceCount - static_cast<int32_t>(rest_indices.size());
				const bool b_1 = (g_best_turn <= simulation_turn && put_count <= rest_count);
				const bool b_2 = (put_count != Parameter::CandidatePieceCount);
				const bool b_3 = (simulation_turn != Parameter::GameTurnLimit);
				return !b_1 && b_2 && b_3;
			};

			while (is_continue()) {
				++simulation_turn;
				oven_clone.Update();
				g_put_infos_2.clear();
				for (int32_t piece_index : rest_indices) {
					vector<PutInfo> npis_2 = GetPutableInfos(
						simulation_turn,
						piece_index,
						CandidateLaneType_Large,
						large_pieces[piece_index],
						oven_clone
					);
					if (npis_2.empty()) {
						continue;
					}
					move(npis_2.begin(), npis_2.end(), back_inserter(g_put_infos_2));
				}
				if (g_put_infos_2.empty()) {
					continue;
				}
				sort(g_put_infos_2.begin(), g_put_infos_2.end(), greater<PutInfo>());
				const PutInfo npi = g_put_infos_2.front();
				oven_clone.PutPiece(npi);
				LinearUnstableFastErase(npi.piece_index, rest_indices);
				history.push_back(move(npi));
			}

			const bool ok = (simulation_turn < g_best_turn ||
				g_reserved_larges.size() < history.size());

			if (!ok) {
				continue;
			}

			success = true;

			g_best_turn = simulation_turn;

			g_reserved_larges = move(history);

		}

		if (!success) {
			return;
		}


		vector<int32_t> piece_indices;
		piece_indices.reserve(g_reserved_larges.size());
		for (const PutInfo& reserved_large : g_reserved_larges) {
			piece_indices.push_back(reserved_large.piece_index);
		}
		const int32_t reserved_large_count = static_cast<int32_t>(g_reserved_larges.size());
		for (int32_t outer = 0; outer < reserved_large_count; ++outer) {
			const int32_t outer_index = piece_indices[outer];
			for (int32_t inner = outer + 1; inner < reserved_large_count; ++inner) {
				const int32_t inner_index = piece_indices[inner];
				if (inner_index < outer_index) {
					continue;
				}
				--(g_reserved_larges[inner].piece_index);
			}
		}

		reverse(g_reserved_larges.begin(), g_reserved_larges.end());
	}

	PutInfo NextSmall() {
		int32_t turn = g_stage->turn();
		const CandidatePieces& small_pieces = g_stage->candidateLane(CandidateLaneType_Small).pieces();
		g_put_infos_3.clear();
		for (int32_t piece_index = 0; piece_index < Parameter::CandidatePieceCount; ++piece_index) {
			vector<PutInfo> p = GetPutableInfos(
				turn,
				piece_index,
				CandidateLaneType_Small,
				small_pieces[piece_index],
				g_oven
			);
			if (p.empty()) {
				continue;
			}
			move(p.begin(), p.end(), back_inserter(g_put_infos_3));
		}
		if (g_put_infos_3.empty()) {
			return PutInfo::Invalid();
		}
		sort(g_put_infos_3.begin(), g_put_infos_3.end(), greater<PutInfo>());
		const float filled = (static_cast<float>(g_oven.GetCellCount() / static_cast<float>(Parameter::OvenCellCount)));
		const float threshold = (filled * 0.25f);
		for (const PutInfo& small : g_put_infos_3) {
			if (small.evaluation < threshold) {
				break;
			}
			bool ok = true;
			for (const PutInfo& large : g_reserved_larges) {
				if (small.IsAbleToPut(turn, large)) {
					continue;
				}
				ok = false;
				break;
			}
			if (!ok) {
				continue;
			}
			return small;
		}
		return PutInfo::Invalid();
	}



	//------------------------------------------------------------------------------
	/// コンストラクタ。
	/// @detail 最初のステージ開始前に実行したい処理があればここに書きます。
	Answer::Answer()
	{
		g_put_infos_1.reserve(1000);    // 調整
		g_put_infos_2.reserve(1000);    // 調整
		g_put_infos_3.reserve(1000);    // 調整
		g_put_infos_4.reserve(1000);    // 調整
										//g_put_infos_5.reserve(Parameter::CandidatePieceCount);
	}

	//------------------------------------------------------------------------------
	/// デストラクタ。
	/// @detail 最後のステージ終了後に実行したい処理があればここに書きます。
	Answer::~Answer()
	{
		OUTPUT_PUT_COUNT("TotalLarge: ", g_total_put_large_count);
		OUTPUT_PUT_COUNT("TotalSmall: ", g_total_put_small_count);
	}
	//------------------------------------------------------------------------------
	/// 各ステージ開始時に呼び出される処理。
	/// @detail 各ステージに対する初期化処理が必要ならここに書きます。
	/// @param aStage 現在のステージ。
	void Answer::init(const Stage& stage)
	{

		ADD_INT(g_stage_count, 1);
		ASSIGN_INT(g_large_put_count, 0);
		ASSIGN_INT(g_small_put_count, 0);

		g_stage = &stage;

		g_oven.Initialize();

		g_pre_put_lane_type = CandidateLaneType_TERM;

		g_best_turn = Parameter::GameTurnLimit;

		for (CandidateLaneType lane_type : g_lane_types) {
			g_rhtc_smoother[lane_type].Initialize();
			const CandidatePieces& pieces = stage.candidateLane(lane_type).pieces();
			for (const Piece& piece : pieces) {
				g_rhtc_smoother[lane_type].Add(piece.requiredHeatTurnCount());
			}
		}

	}
	//------------------------------------------------------------------------------
	/// このターンでの行動を指定する。
	/// @detail 希望する行動を Action の static 関数で生成して return してください。
	///         正常ではない行動を return した場合、何も起きません。
	///         詳細は Action のヘッダを参照してください。
	/// @param aStage 現在のステージ。
	Action Answer::decideNextAction(const Stage& stage)
	{

		const int32_t turn = stage.turn();
		OUTPUT_TURN_COUNT(turn);

		g_oven.Update();

		if (g_pre_put_lane_type != CandidateLaneType_TERM) {
			const Piece& new_piece = stage.candidateLane(g_pre_put_lane_type).pieces()[g_max_piece_index];
			g_rhtc_smoother[g_pre_put_lane_type].Add(new_piece.requiredHeatTurnCount());
			g_pre_put_lane_type = CandidateLaneType_TERM;
		}

		const int32_t rest_large_count = static_cast<int32_t>(g_reserved_larges.size());
		const bool reserve_large = (rest_large_count != Parameter::CandidatePieceCount);
		if (reserve_large) {
			ReserveLarges();
		}

		PutInfo put_info = PutInfo::Invalid();
		const bool put_large = (!g_reserved_larges.empty() && g_reserved_larges.back().put_turn == turn);
		if (put_large) {
			put_info = g_reserved_larges.back();
			g_reserved_larges.pop_back();
		}

		const bool put_small = !put_info;
		if (put_small) {
			put_info = NextSmall();
		}

		if (!put_info) {
			g_pre_put_lane_type = CandidateLaneType_TERM;
			return Action::Wait();
		}


		const int32_t piece_index = put_info.piece_index;
		const CandidateLaneType lane_type = put_info.lane_type;
		const Vector2i& position = put_info.position;
		const Piece& piece = stage.candidateLane(lane_type).pieces()[piece_index];
		g_pre_put_lane_type = put_info.lane_type;
		g_oven.PutPiece(piece, position);
		ADD_PUT_COUNT(lane_type, g_small_put_count, g_large_put_count);
		PRINT_PUT_COOKIE(turn, piece.width(), piece.height(), position, g_oven);
		CHECK_INTERSECT(g_stage_count, stage, piece.width(), piece.height(), position, g_oven);
		return Action::Put(lane_type, piece_index, position);
	}

	//------------------------------------------------------------------------------
	/// 各ステージ終了時に呼び出される処理。
	/// @detail 各ステージに対する終了処理が必要ならここに書きます。
	/// @param aStage 現在のステージ。
	void Answer::finalize(const Stage& aStage)
	{
		OUTPUT_STAGE_COUNT(g_stage_count);

		ADD_INT(g_total_put_large_count, g_large_put_count);
		OUTPUT_PUT_COUNT("Large: ", g_large_put_count);

		ADD_INT(g_total_put_small_count, g_small_put_count);
		OUTPUT_PUT_COUNT("Small: ", g_small_put_count);
	}

} // namespace
  // EOF