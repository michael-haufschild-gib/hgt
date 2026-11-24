import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.WindowSize

/-! # Converting a common-divisor inequality to a precision exponent -/

open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
noncomputable section

/-- If a common modulus costs (1+b) log d, while the visit supplies
log ε + b log v plus a constant, every larger exponent is excluded. -/
theorem eventual_divisor_rate {v : ℝ → ℝ} {D b A h : ℝ} (hb : 0 ≤ b) (hA : 0 < A)
    (hgap : b*D-1 < (1+b)*h)
    (hv : Tendsto (fun ε => log (v ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 D)) (C : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ d : ℕ,
      (1+b)*log (d:ℝ) ≤ C+log (A*ε)+b*log (v ε) → log (d:ℝ)/log (1/ε) < h := by
  have ht := ((tendsto_const_div_log_one_div (C+log A)).add (hv.const_mul b)).sub_const 1
  rw [zero_add] at ht
  filter_upwards [ht.eventually_lt_const hgap,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε he
  intro d hd
  have hl := log_pos ((one_lt_div he.1).mpr he.2)
  have hb' : 0 < 1+b := by positivity
  have hlog : log ε = -log (1/ε) := by rw [one_div,log_inv,neg_neg]
  rw [log_mul hA.ne' he.1.ne',hlog] at hd
  apply (mul_lt_mul_iff_right₀ hb').mp
  apply lt_of_le_of_lt _ hε
  change (1+b)*(log (d:ℝ)/log (1/ε)) ≤ (C+log A)/log (1/ε)+b*(log (v ε)/log (1/ε))-1
  have hx := div_le_div_of_nonneg_right hd hl.le
  calc (1+b)*(log (d:ℝ)/log (1/ε)) = ((1+b)*log (d:ℝ))/log (1/ε) := by ring
       _ ≤ _ := hx
       _ = _ := by field_simp [hl.ne']; ring

/-- The limiting exponent when n independent ratios are measured. -/
theorem choose_ratio_slack {n : ℕ} (hn : 0 < n) {D h : ℝ}
    (hh : (D-(n:ℝ))/((n:ℝ)+1) < h) :
    ∃ η > (0:ℝ), (((n:ℝ))⁻¹+η)*D-1 < (1+(((n:ℝ))⁻¹+η))*h := by
  have hn' := Nat.cast_pos (α:=ℝ).mpr hn
  have hlim : (n:ℝ)⁻¹*D-1 < (1+(n:ℝ)⁻¹)*h := by
    have hpos : 0 < (n:ℝ)+1 := by positivity
    have hlt := (div_lt_iff₀ hpos).mp hh
    apply (mul_lt_mul_iff_right₀ hn').mp
    calc (n:ℝ)*((n:ℝ)⁻¹*D-1) = D-n := by field_simp [hn'.ne']
         _ < h*((n:ℝ)+1) := hlt
         _ = (n:ℝ)*((1+(n:ℝ)⁻¹)*h) := by field_simp [hn'.ne']
  have hc (f : ℝ → ℝ) (h : Continuous f) : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)) :=
    (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have h₁ := hc (fun x => (((n:ℝ))⁻¹+x)*D-1) (by fun_prop)
  have h₂ := hc (fun x => (1+(((n:ℝ))⁻¹+x))*h) (by fun_prop)
  have he := h₁.eventually_lt h₂ (by simpa only [add_zero] using hlim)
  have hp : ∀ᶠ x in 𝓝[>] (0:ℝ), 0<x := self_mem_nhdsWithin
  exact (hp.and he).exists

#print axioms eventual_divisor_rate
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
