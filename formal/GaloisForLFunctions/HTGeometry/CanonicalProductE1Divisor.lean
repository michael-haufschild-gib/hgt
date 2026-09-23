/-
# The divisor of the arbitrarily indexed genus-one canonical product

The genus-one product `∏_i E₁(z / a i)` vanishes at a point exactly to the multiplicity of that
point in the index family.  The proof splits the index into the fiber over the point and its
complement: the fiber contributes a pure power of `E₁(z / w)`, whose order at `w` is one, and the
complement contributes a factor that does not vanish at `w`.
-/
import GaloisForLFunctions.HTGeometry.CanonicalProduct
import GaloisForLFunctions.HTGeometry.CountableDivisorConvergenceExponent

noncomputable section

open Filter Topology Set Metric
open GaloisForLFunctions.CountableDivisor

namespace RHTower

variable {ι : Type*}

theorem multipliable_canonicalProductE1Indexed {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) (z : ℂ) :
    Multipliable (fun i : ι => weierstrassE1 (z / a i)) := by
  have hfsum : Summable (fun i : ι => weierstrassE1 (z / a i) - 1) :=
    (canonicalProductE1Indexed_sub_one_norm_summable a hane hsum z).of_norm
  have hm : Multipliable (fun i : ι => 1 + (weierstrassE1 (z / a i) - 1)) :=
    Complex.multipliable_one_add_of_summable hfsum
  refine hm.congr (fun i => ?_)
  ring

theorem canonicalProductE1Indexed_split {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) (s : Set ι) (z : ℂ) :
    (∏' x : s, weierstrassE1 (z / a x)) * (∏' x : ↑(sᶜ), weierstrassE1 (z / a x))
      = canonicalProductE1Indexed a z := by
  have h1 : Multipliable (fun x : s => weierstrassE1 (z / a x.1)) :=
    multipliable_canonicalProductE1Indexed (a := fun x : s => a x.1)
      (fun x => hane x.1) (hsum.subtype (· ∈ s)) z
  have h2 : Multipliable (fun x : ↑(sᶜ) => weierstrassE1 (z / a x.1)) :=
    multipliable_canonicalProductE1Indexed (a := fun x : ↑(sᶜ) => a x.1)
      (fun x => hane x.1) (hsum.subtype (· ∈ sᶜ)) z
  exact Multipliable.tprod_mul_tprod_compl
    (f := fun i : ι => weierstrassE1 (z / a i)) h1 h2

theorem tprod_fiber_weierstrassE1_eq {a : ι → ℂ} (hloc : LocallyFiniteDivisor a) (w z : ℂ) :
    (∏' x : ({i : ι | a i = w} : Set ι), weierstrassE1 (z / a x))
      = weierstrassE1 (z / w) ^ ({i : ι | a i = w}.ncard) := by
  haveI : Fintype ({i : ι | a i = w} : Set ι) := (finite_fiber hloc w).fintype
  have hcongr : ∀ x : ({i : ι | a i = w} : Set ι),
      weierstrassE1 (z / a x) = weierstrassE1 (z / w) := by
    intro x
    rw [x.2]
  rw [tprod_congr hcongr, tprod_fintype, Finset.prod_const, Finset.card_univ]
  congr 1
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

theorem canonicalProductE1Indexed_eq_pow_mul {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ)))
    (hloc : LocallyFiniteDivisor a) (w : ℂ) :
    canonicalProductE1Indexed a
      = (fun z : ℂ => weierstrassE1 (z / w) ^ ({i : ι | a i = w}.ncard))
        * canonicalProductE1Indexed (fun x : ↑(({i : ι | a i = w} : Set ι)ᶜ) => a x.1) := by
  funext z
  rw [Pi.mul_apply, ← canonicalProductE1Indexed_split hane hsum {i : ι | a i = w} z,
    tprod_fiber_weierstrassE1_eq hloc w z]
  rfl

/-- The genus-one factor has a simple zero at the prescribed point. -/
theorem analyticOrderAt_weierstrassE1_div {w : ℂ} (hw : w ≠ 0) :
    analyticOrderAt (fun z : ℂ => weierstrassE1 (z / w)) w = 1 := by
  have han : AnalyticAt ℂ (fun z : ℂ => weierstrassE1 (z / w)) w := by
    simp only [weierstrassE1]
    fun_prop
  have hE : HasDerivAt weierstrassE1 (-Complex.exp 1) 1 := by
    have hraw :=
      ((hasDerivAt_const (x := (1 : ℂ)) (c := (1 : ℂ))).sub (hasDerivAt_id 1)).mul
        (Complex.hasDerivAt_exp 1)
    convert! hraw using 1
    simp
  have hdiv : HasDerivAt (fun z : ℂ => z / w) (1 / w) w := by
    simpa using (hasDerivAt_id w).div_const w
  have hFderiv : HasDerivAt (fun z : ℂ => weierstrassE1 (z / w)) ((-Complex.exp 1) * (1 / w)) w := by
    have hE' : HasDerivAt weierstrassE1 (-Complex.exp 1) ((fun z : ℂ => z / w) w) := by
      simpa only [div_self hw] using hE
    simpa only [Function.comp_def] using hE'.comp (h := fun z : ℂ => z / w) w hdiv
  refine han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_
  · simp only [div_self hw, weierstrassE1_one]
  · rw [hFderiv.deriv]
    exact mul_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero 1)) (one_div_ne_zero hw)

/-- **The divisor of the genus-one canonical product.**  Its order at every nonzero point is
exactly the multiplicity of that point in the index family. -/
theorem analyticOrderAt_canonicalProductE1Indexed {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hloc : LocallyFiniteDivisor a) (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ)))
    {w : ℂ} (hw : w ≠ 0) :
    analyticOrderAt (canonicalProductE1Indexed a) w = (({i : ι | a i = w}.ncard : ℕ) : ℕ∞) := by
  set F : Set ι := {i : ι | a i = w} with hF
  set T : ↑(Fᶜ) → ℂ := fun x => a x.1 with hT
  have hTane : ∀ x : ↑(Fᶜ), T x ≠ 0 := fun x => hane x.1
  have hTsum : Summable (fun x : ↑(Fᶜ) => 1 / ‖T x‖ ^ (2 : ℕ)) := hsum.subtype (· ∈ Fᶜ)
  have hTne : ∀ x : ↑(Fᶜ), w ≠ T x := by
    intro x
    have hx := x.2
    simp only [hF, Set.mem_compl_iff, Set.mem_setOf_eq] at hx
    exact fun h => hx h.symm
  have hQne : canonicalProductE1Indexed T w ≠ 0 :=
    canonicalProductE1Indexed_ne_zero T hTane hTsum hTne
  have hQan : AnalyticAt ℂ (canonicalProductE1Indexed T) w :=
    canonicalProductE1Indexed_analytic T hTane hTsum w (Set.mem_univ _)
  have hbase : AnalyticAt ℂ (fun z : ℂ => weierstrassE1 (z / w)) w := by
    simp only [weierstrassE1]
    fun_prop
  have hGan : AnalyticAt ℂ (fun z : ℂ => weierstrassE1 (z / w) ^ (F.ncard)) w := hbase.pow _
  have hsplit := canonicalProductE1Indexed_eq_pow_mul hane hsum hloc w
  rw [hsplit, analyticOrderAt_mul hGan hQan, hQan.analyticOrderAt_eq_zero.mpr hQne, add_zero]
  have hpow : (fun z : ℂ => weierstrassE1 (z / w) ^ (F.ncard))
      = (fun z : ℂ => weierstrassE1 (z / w)) ^ (F.ncard) := by
    funext z
    rw [Pi.pow_apply]
  rw [hpow, analyticOrderAt_pow hbase, analyticOrderAt_weierstrassE1_div hw]
  simp

theorem canonicalProductE1Indexed_zero {a : ι → ℂ} : canonicalProductE1Indexed a 0 = 1 := by
  rw [canonicalProductE1Indexed]
  calc (∏' i : ι, weierstrassE1 (0 / a i)) = ∏' _i : ι, (1 : ℂ) := by
        exact tprod_congr (fun i => by rw [zero_div, weierstrassE1_zero])
    _ = 1 := tprod_one

end RHTower
