import GaloisForLFunctions.HTGeometry.NevanlinnaRamification
import GaloisForLFunctions.HTGeometry.DriftCharacteristicGrowth
import Mathlib.Analysis.Meromorphic.IsolatedZeros

/-!
# Drifting primitives have no totally ramified finite value

If `W` is entire and `W(z+T) = W(z)+C` with `T` and `C` nonzero, then a single totally ramified
value `a` produces the whole arithmetic progression `a + Cℤ` of totally ramified values.  Five of
them are `‖C‖`-separated, which contradicts Nevanlinna's ramification bound — unless `W` is affine,
in which case its derivative never vanishes and no value is ramified at all.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real Set Filter ValueDistribution MeromorphicOn

/-- An entire function whose meromorphic order is infinite at one point vanishes identically. -/
theorem eq_zero_of_meromorphicOrderAt_eq_top {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z : ℂ} (h : meromorphicOrderAt f z = ⊤) (w : ℂ) : f w = 0 := by
  have hfan : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  rw [meromorphicOrderAt_eq_top_iff] at h
  have hfr : ∃ᶠ x in nhdsWithin z {z}ᶜ, f x = 0 := h.frequently
  exact hfan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) hfr (Set.mem_univ w)

/-- **Drifting primitives have no totally ramified finite value.**  The drift moves a totally
ramified value along the arithmetic progression `a + Cℤ`, producing five separated ramified values
where the Nevanlinna bound allows at most four. -/
theorem not_totallyRamified_of_drift {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    {T C : ℂ} (hT : T ≠ 0) (hC : C ≠ 0)
    (hdrift : ∀ z, W (z + T) = W z + C) (a : ℂ) :
    ¬ TotallyRamified W a := by
  classical
  intro ha
  have hk0 : C / T ≠ 0 := div_ne_zero hC hT
  by_cases haffine : ∀ z, W z + (-(C / T) * z - W 0) = 0
  · -- `W` is affine with slope `C/T ≠ 0`, so no value is ramified
    have hWaff : W = fun z => (C / T) * z + W 0 := by
      funext z
      have h := haffine z
      linear_combination h
    set z₀ : ℂ := (a - W 0) / (C / T) with hz₀
    have hval : W z₀ = a := by
      rw [hWaff]
      simp only [hz₀]
      field_simp
      ring
    have hderiv : deriv W z₀ = C / T := by
      rw [hWaff]
      simp
    have := ha z₀ hval
    rw [hderiv] at this
    exact hk0 this
  · push_neg at haffine
    obtain ⟨z₀, hz₀⟩ := haffine
    -- the difference from the affine part does not vanish identically
    have hgo : ∀ z, meromorphicOrderAt (fun w => W w + (-(C / T) * w - W 0)) z ≠ ⊤ := by
      intro z hcon
      have hgdiff : Differentiable ℂ fun w => W w + (-(C / T) * w - W 0) :=
        hW.add (((differentiable_const _).mul differentiable_id).sub (differentiable_const _))
      exact hz₀ (eq_zero_of_meromorphicOrderAt_eq_top hgdiff hcon z₀)
    obtain ⟨hTtop, hTlog⟩ := drift_characteristic_growth hW hT hdrift hgo
    -- five separated totally ramified values
    let A : Fin 5 → ℂ := fun j => a + ((j : ℕ) : ℤ) • C
    have hAdef : ∀ j : Fin 5, A j = a + ((j : ℕ) : ℤ) • C := fun j => rfl
    have hsep : ∀ i j : Fin 5, i ≠ j → ‖C‖ ≤ ‖A i - A j‖ := by
      intro i j hij
      have hdiff : A i - A j = ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : ℂ) * C := by
        rw [hAdef, hAdef]
        simp only [zsmul_eq_mul]
        push_cast
        ring
      have hne : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ≠ 0 := by
        rw [sub_ne_zero]
        intro hcon
        exact hij (Fin.ext (by exact_mod_cast hcon))
      have hone : (1 : ℝ) ≤ ‖((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : ℂ)‖ := by
        rw [Complex.norm_intCast]
        have h1 : (1 : ℤ) ≤ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| := Int.one_le_abs hne
        have h2 : ((1 : ℤ) : ℝ) ≤ ((|((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| : ℤ) : ℝ) := by
          exact_mod_cast h1
        rw [Int.cast_abs] at h2
        simpa using h2
      rw [hdiff, norm_mul]
      nlinarith [norm_nonneg C, norm_pos_iff.mpr hC, hone]
    have hram : ∀ j : Fin 5, ∀ z, W z = A j → deriv W z = 0 := by
      intro j z hz
      rw [hAdef] at hz
      exact totallyRamified_add_zsmul (W := W) (T := T) (C := C) hdrift ha ((j : ℕ) : ℤ) z hz
    -- the nondegeneracy hypotheses
    have hWne : ∃ z, W z ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h := hdrift 0
      rw [hcon (0 + T), hcon 0] at h
      exact hC (by linear_combination -h)
    have hf0 : ∀ z, meromorphicOrderAt W z ≠ ⊤ := by
      intro z hcon
      obtain ⟨w, hw⟩ := hWne
      exact hw (eq_zero_of_meromorphicOrderAt_eq_top hW hcon w)
    have hfa : ∀ j : Fin 5, ∀ z, meromorphicOrderAt (fun w => W w - A j) z ≠ ⊤ := by
      intro j z hcon
      have hdiff : Differentiable ℂ fun w => W w - A j := hW.sub (differentiable_const _)
      have h0 := eq_zero_of_meromorphicOrderAt_eq_top hdiff hcon
      have hconst : ∀ w, W w = A j := by
        intro w
        have := h0 w
        linear_combination this
      have h := hdrift 0
      rw [hconst (0 + T), hconst 0] at h
      exact hC (by linear_combination -h)
    have hfd : ∀ z, meromorphicOrderAt (deriv W) z ≠ ⊤ := by
      intro z hcon
      have hdiff : Differentiable ℂ (deriv W) := by
        have hfan : AnalyticOnNhd ℂ W Set.univ := hW.differentiableOn.analyticOnNhd isOpen_univ
        exact fun x => ((hfan.deriv) x (Set.mem_univ x)).differentiableAt
      have h0 := eq_zero_of_meromorphicOrderAt_eq_top hdiff hcon
      have hconst : ∀ x y : ℂ, W x = W y :=
        fun x y => is_const_of_deriv_eq_zero hW h0 x y
      have h := hdrift 0
      rw [hconst (0 + T) 0] at h
      exact hC (by linear_combination -h)
    have hcod : ∀ r : ℝ, ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv W z ≠ 0 := by
      intro r
      have hfan : AnalyticOnNhd ℂ W Set.univ := hW.differentiableOn.analyticOnNhd isOpen_univ
      have hdan : AnalyticOnNhd ℂ (deriv W) Set.univ := hfan.deriv
      have hmero : MeromorphicOn (deriv W) (sphere (0 : ℂ) |r|) :=
        fun x _ => (hdan x (Set.mem_univ x)).meromorphicAt
      exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero hmero fun u _ => hfd u
    have hfinal := card_totallyRamified_le_four hW A (norm_pos_iff.mpr hC) hsep hram hf0 hfa hfd
      hcod hTlog hTtop
    norm_num at hfinal

/-- **The quadratic matching residue is unreachable.**  A drifting primitive is never of the form
`a + g²` for an entire `g`: every `a`-point of such a function is a double point, so `a` would be a
totally ramified value. -/
theorem not_quadratic_matching_of_drift {W g : ℂ → ℂ} (hW : Differentiable ℂ W)
    (hg : Differentiable ℂ g) {T C : ℂ} (hT : T ≠ 0) (hC : C ≠ 0)
    (hdrift : ∀ z, W (z + T) = W z + C) (a : ℂ) :
    ¬ (∀ z, W z = a + g z ^ 2) := by
  intro hsq
  refine not_totallyRamified_of_drift hW hT hC hdrift a ?_
  intro z hz
  have hgz : g z = 0 := by
    have h := hsq z
    rw [hz] at h
    have : g z ^ 2 = 0 := by linear_combination -h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hWfun : W = fun w => a + g w ^ 2 := funext hsq
  have hderiv : HasDerivAt (fun w => a + g w ^ 2) (2 * g z * deriv g z) z := by
    have hgd : HasDerivAt g (deriv g z) z := (hg z).hasDerivAt
    have hsq' : HasDerivAt (fun w => g w ^ 2) (2 * g z ^ (2 - 1) * deriv g z) z := hgd.pow 2
    simpa using hsq'.const_add a
  rw [hWfun, hderiv.deriv, hgz]
  ring

/-- **The Briot–Bouquet normal form drifts.**  A function of the form `c₀ z + M(exp(αz))` changes by
the constant `c₀ · 2πi/α` along the period of the exponential. -/
theorem drift_of_exp_normalForm {M : ℂ → ℂ} {c₀ α : ℂ} (hα : α ≠ 0) (z : ℂ) :
    (fun w => c₀ * w + M (Complex.exp (α * w))) (z + 2 * Real.pi * Complex.I / α)
      = (fun w => c₀ * w + M (Complex.exp (α * w))) z + c₀ * (2 * Real.pi * Complex.I / α) := by
  have harg : α * (z + 2 * Real.pi * Complex.I / α) = α * z + 2 * Real.pi * Complex.I := by
    field_simp
  have hexp : Complex.exp (α * (z + 2 * Real.pi * Complex.I / α)) = Complex.exp (α * z) := by
    rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  simp only
  rw [hexp]
  ring

end GaloisForLFunctions.HTGeometry
