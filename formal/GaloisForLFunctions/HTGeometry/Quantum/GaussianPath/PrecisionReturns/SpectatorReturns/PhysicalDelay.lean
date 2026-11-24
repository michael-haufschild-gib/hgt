import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.OneGateDate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.FirstWait
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.BasisCost

/-! # Physical circuit cost at the first spectral one-gate return -/

open Real Filter MeasureTheory Set Matrix
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
noncomputable section

/-- The precision exponent of a quotient of two growing clocks is the
difference of their exponents, also for elapsed waits with a fixed cutoff. -/
theorem log_ratio_of_exponents {u v : ℝ→ℝ} {x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hu : Tendsto (fun ε => log (u ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 x))
    (hv : Tendsto (fun ε => log (v ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 y)) :
    Tendsto (fun ε => log (u ε/v ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 (x-y)) := by
  refine (hu.sub hv).congr' ?_
  filter_upwards [hu.eventually_const_lt hx,hv.eventually_const_lt hy] with ε h₁ h₂
  have hn (z : ℝ) (hh : 0 < log z/log (1/ε)) : z≠0 := by
    rintro rfl
    simp only [log_zero,zero_div,lt_self_iff_false] at hh
  change log _/log (1/ε)-log _/log (1/ε)=_
  rw [log_div (hn _ h₁) (hn _ h₂),sub_div]

/-- Relative to the first one-gate date in a free basis, every physical
budget below the spanning count returns later by a factor with precision
exponent three. Changing physical error by a constant preserves the law. -/
theorem gaussian_physical_delay :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩
      ∀ a > (0:ℝ), ∀ s : ℕ, s+1<N → ∀ c > (0:ℝ),
        Tendsto (fun ε => log (firstVisit H a s (c*ε)/SpectralApproximation.firstVisit H a 1 ε)/log (1/ε))
          (𝓝[>] 0) (𝓝 3) := by
  filter_upwards [gaussian_one_gate_dates,gaussian_gap_clock,DisconnectedReturns.gaussian_disconnected_scalar_return]
    with ω hfree hgap hdisc k
  intro N H a ha s hs c hc
  obtain ⟨e,hg,hy⟩ := hgap k
  obtain ⟨A,hA,hctrl⟩ := hdisc (k+1)
  have hb : s<k+1+1 := by dsimp only [N] at hs; omega
  have hp := exponent_of_scalar_control H e s hA (fun t ε => hctrl t ε s hb) hg hy ha
  have hD : 8 ≤ (2:ℕ)^N := (by decide : 8 ≤ 2^3).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp only [N]; omega))
  have h := log_ratio_of_exponents (show 0<((2^N-3+1:ℕ):ℝ) by positivity)
    (by exact_mod_cast (show 0<2^N-5 by omega)) (Jumps.scaled_exponent hc hp) (hfree k a ha).1
  have he : ((2^N-3+1:ℕ):ℝ)-((2^N-5:ℕ):ℝ)=3 := by
    apply sub_eq_iff_eq_add.mpr
    exact_mod_cast (show 2^N-3+1=3+(2^N-5) by omega)
  rw [he] at h
  exact h

/-- At the first one-gate return in a free basis, a physically implemented
change of basis and its inverse must together supply the spanning cost,
even when the basis can be approximated to any fixed multiple of ε. -/
theorem gaussian_cost_of_first_fitting_basis :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩
      ∀ a > (0:ℝ), ∀ c > (0:ℝ), ∀ᶠ ε in 𝓝[>] (0:ℝ),
        let v := SpectralApproximation.firstVisit H a 1 ε
        let U := unitaryEvolution H.val v
        v ∈ SpectralApproximation.affordableDates H 1 ε ∧
          ∀ (W : unitaryGroup (Fin N→Bool) ℂ) (b j : ℕ),
            HasProjectiveCircuitApproximation N (c*ε) b W.val →
            HasProjectiveCircuitApproximation N ε j (W.val*U*star W.val) → N-1 ≤ 2*b+j := by
  filter_upwards [gaussian_physical_delay] with ω h k
  intro N H a ha c hc
  let C := 1+2*c
  have hC : 0<C := by dsimp only [C]; positivity
  have hs : (N-2)+1<N := by dsimp only [N]; omega
  filter_upwards [(h k a ha (N-2) hs C hC).eventually_const_lt (by norm_num : (0:ℝ)<3),
    Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hh hε
  intro v U
  have hv := (SpectralApproximation.firstVisit_isLeast H a 1 hε.1).1
  refine ⟨hv.2,?_⟩
  intro W b j hW hj
  by_contra! hshort
  have hfit := SpectralApproximation.cost_in_physical_basis
    (⟨U,unitaryEvolution_mem_unitary H.2 v⟩ : unitaryGroup (Fin N→Bool) ℂ) W hW hj
  obtain ⟨z,hz,V,hV,herr⟩ := hfit
  have hle := (firstVisit_isLeast H a (N-2) (mul_pos hC hε.1)).2
    (show v ∈ visitSet H a (N-2) (C*ε) from ⟨hv.1,z,hz,V,by omega,by
      rwa [show C*ε=ε+2*(c*ε) by dsimp only [C]; ring]⟩)
  have hlog := (div_pos_iff_of_pos_right (log_pos ((one_lt_div hε.1).mpr hε.2))).mp hh
  have hratio := Real.log_nonpos (div_nonneg (ha.trans_le (firstVisit_isLeast H a (N-2) (mul_pos hC hε.1)).1.1).le
    (ha.trans_le hv.1).le) ((div_le_one (ha.trans_le hv.1)).mpr hle)
  exact hlog.not_ge hratio

#print axioms gaussian_physical_delay
#print axioms gaussian_cost_of_first_fitting_basis
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
