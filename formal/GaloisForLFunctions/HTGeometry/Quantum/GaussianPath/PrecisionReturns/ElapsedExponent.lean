import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.ChangeOfRadius

/-! # From absolute return dates to elapsed waiting times -/
open Filter Topology Real Set
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns
noncomputable section

/-- Subtracting a fixed positive observation origin preserves a positive
logarithmic first-passage exponent. -/
theorem elapsed_exponent {v : ℝ → ℝ} {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hv : ∀ ε > 0, a ≤ v ε)
    (h : Tendsto (fun ε => log (v ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 d)) :
    Tendsto (fun ε => log (v ε-a)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 d) := by
  have hb := (tendsto_const_div_log_one_div (log (2*a))).eventually_lt_const (half_pos hd)
  have hl := h.eventually_const_lt (half_lt_self hd)
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 2*a < v ε ∧ 0 < log (1/ε) := by
    filter_upwards [hb,hl,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε h1 h2 hε
    have hlog := log_pos ((one_lt_div hε.1).mpr hε.2)
    have hh := (div_lt_div_iff_of_pos_right hlog).mp (h1.trans h2)
    exact ⟨(log_lt_log_iff (by positivity : 0<2*a) (ha.trans_le (hv ε hε.1))).mp hh,hlog⟩
  have hh := h.sub (tendsto_const_div_log_one_div (log 2))
  rw [sub_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hh h
  · filter_upwards [he] with ε hε
    have hm : v ε/2 ≤ v ε-a := by linarith only [hε.1]
    have hp : 0 < v ε/2 := by linarith only [hε.1,ha]
    rw [←sub_div,←log_div (by linarith only [hp]) (by norm_num)]
    exact div_le_div_of_nonneg_right (log_le_log hp hm) hε.2.le
  · filter_upwards [he] with ε hε
    exact div_le_div_of_nonneg_right (log_le_log (by linarith only [hε.1,ha]) (sub_le_self _ ha.le)) hε.2.le

end
end GaloisForLFunctions.HTGeometry.PrecisionReturns
