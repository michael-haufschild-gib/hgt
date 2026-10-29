import GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
import GaloisForLFunctions.HTGeometry.CombinationModeDiophantineDivisor
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.PSeries

/-!
# Schwartz Poisson summation in arbitrary dimension

A product of reciprocal quadratic weights controls all integer translates of a
Schwartz function, uniformly on bounded translation sets. The same estimate for
its Fourier transform supplies absolute convergence on the dual lattice.
Normal periodization and torus Fourier inversion then give both ordinary and
twisted Poisson summation without additional convergence assumptions.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform Topology

namespace GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

variable {ι : Type*} [Fintype ι]

local notation "X" => ι → ℝ
local notation "Z" => ι → ℤ
local notation "E" => EuclideanSpace ℝ ι
local notation "ip" => integerPoint (ι := ι)
local notation "q" => torusProjection (ι := ι)

/-- The coordinatewise integer lattice in Euclidean space. -/
def euclideanIntegerPoint (n : Z) : E := WithLp.toLp 2 (ip n)

private def weight (n : Z) : ℝ := ∏ i, (1 + |(n i : ℝ)|)

private theorem weight_pos (n : Z) : 0 < weight n :=
  Finset.prod_pos (fun _ _ => by positivity)

private theorem reciprocal_summable : Summable (fun n : Z => 1 / (weight n) ^ 2) := by
  classical
  have hn : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    simpa only [Real.rpow_two, sq_abs, add_comm] using h
  have hz : Summable (fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ 2) := by
    rw [summable_int_iff_summable_nat_and_neg]
    simpa using And.intro hn hn
  let b : ℤ → ℝ := fun n => 1 / (1 + |(n : ℝ)|) ^ 2
  have hb : Summable b := hz
  have hb0 : ∀ n, 0 ≤ b n := fun n => by dsimp only [b]; positivity
  have hs := summable_prod_pi (fun _ : Fin (Fintype.card ι) => b)
    (fun _ => hb0) (fun _ => hb)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let e' : Z ≃ (Fin (Fintype.card ι) → ℤ) :=
    { toFun n j := n (e.symm j)
      invFun n i := n (e i)
      left_inv n := by funext i; simp
      right_inv n := by funext j; simp }
  refine (hs.comp_injective e'.injective).congr fun n => ?_
  change (∏ j : Fin (Fintype.card ι), b (n (e.symm j))) = _
  rw [Fintype.prod_equiv e.symm (fun j => b (n (e.symm j)))
    (fun i => b (n i)) (fun _ => rfl)]
  simp only [weight, b, one_div, Finset.prod_pow, Finset.prod_inv_distrib]

private theorem translated_bound (f : SchwartzMap E ℂ)
    (R : ℝ) (hR : 0 ≤ R) (x : X) (hx : ‖x‖ ≤ R) (n : Z) :
    ‖f (WithLp.toLp 2 (x + ip n))‖ ≤
      ((1 + R) ^ (2 * Fintype.card ι) *
        (2 ^ (2 * Fintype.card ι) * (Finset.Iic (2 * Fintype.card ι, 0)).sup
          (schwartzSeminormFamily ℂ E ℂ) f)) / (weight n) ^ 2 := by
  let y : E := WithLp.toLp 2 (x + ip n)
  have hi (i : ι) : 1 + |(n i : ℝ)| ≤ (1 + R) * (1 + ‖y‖) := by
    have hiX : ‖x i‖ ≤ R := (norm_le_pi_norm x i).trans hx
    have hiY : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
    have he : |(n i : ℝ)| = ‖y i - x i‖ := by simp [y, integerPoint]
    have hh : |(n i : ℝ)| ≤ ‖y‖ + R := by
      rw [he]
      exact (norm_sub_le _ _).trans (add_le_add hiY hiX)
    nlinarith only [hh, mul_nonneg hR (norm_nonneg y)]
  have hw : weight n ≤ ((1 + R) * (1 + ‖y‖)) ^ Fintype.card ι := by
    calc
      _ ≤ ∏ _ : ι, (1 + R) * (1 + ‖y‖) :=
        Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => hi i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ]
  have hw2 : (weight n) ^ 2 ≤
      (1 + R) ^ (2 * Fintype.card ι) * (1 + ‖y‖) ^ (2 * Fintype.card ι) := by
    calc
      _ ≤ (((1 + R) * (1 + ‖y‖)) ^ Fintype.card ι) ^ 2 :=
        pow_le_pow_left₀ (weight_pos n).le hw 2
      _ = _ := by rw [← pow_mul, Nat.mul_comm (Fintype.card ι) 2, mul_pow]
  have hd := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (2 * Fintype.card ι, 0)) (k := 2 * Fintype.card ι) (n := 0)
    le_rfl le_rfl f y
  simp only [norm_iteratedFDeriv_zero] at hd
  apply (le_div_iff₀ (pow_pos (weight_pos n) 2)).mpr
  calc
    _ = (weight n) ^ 2 * ‖f y‖ := by ring
    _ ≤ ((1 + R) ^ (2 * Fintype.card ι) *
        (1 + ‖y‖) ^ (2 * Fintype.card ι)) * ‖f y‖ :=
      mul_le_mul_of_nonneg_right hw2 (norm_nonneg _)
    _ = (1 + R) ^ (2 * Fintype.card ι) *
        ((1 + ‖y‖) ^ (2 * Fintype.card ι) * ‖f y‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

/-- A single summable majorant controls all translates in a bounded set. -/
theorem schwartz_summable_translates (f : SchwartzMap E ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ u : Z → ℝ, Summable u ∧
      ∀ x : X, ‖x‖ ≤ R → ∀ n : Z, ‖f (WithLp.toLp 2 (x + ip n))‖ ≤ u n := by
  let C := (1 + R) ^ (2 * Fintype.card ι) *
    (2 ^ (2 * Fintype.card ι) * (Finset.Iic (2 * Fintype.card ι, 0)).sup
      (schwartzSeminormFamily ℂ E ℂ) f)
  refine ⟨fun n => C / (weight n) ^ 2, ?_, fun x hx n => ?_⟩
  · simpa only [mul_one_div] using reciprocal_summable.mul_left C
  · exact translated_bound f R hR x hx n

/-- Every Schwartz function is absolutely summable on the integer lattice. -/
theorem summable_norm_integerPoint (f : SchwartzMap E ℂ) :
    Summable (fun n : Z => ‖f (euclideanIntegerPoint n)‖) := by
  obtain ⟨u, hu, hb⟩ := schwartz_summable_translates f 0 le_rfl
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hu
  intro n
  simpa only [zero_add, euclideanIntegerPoint] using hb 0 (by simp) n

/-- Absolute lattice summability is preserved by arbitrary real translations. -/
theorem summable_norm_integerPoint_add (f : SchwartzMap E ℂ) (a : E) :
    Summable (fun n : Z => ‖f (euclideanIntegerPoint n + a)‖) := by
  simpa only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add] using
    summable_norm_integerPoint (f.compSubConstCLM ℂ (-a))

/-- Product torus characters agree with the Euclidean Fourier phase. -/
theorem integer_character_eq_fourier_phase (k : Z) (x : X) :
    UnitAddTorus.mFourier (-k) (q x) =
      Complex.exp ((-2 * Real.pi * inner ℝ (WithLp.toLp 2 x)
        (euclideanIntegerPoint k) : ℝ) * Complex.I) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusProjection,
    fourier_coe_apply, Pi.neg_apply, Int.cast_neg, Complex.ofReal_one, div_one,
    PiLp.inner_apply, euclideanIntegerPoint, integerPoint, Real.inner_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Integer torus coefficients equal Euclidean Fourier samples. -/
theorem integer_fourier_coefficient (f : E → ℂ) (k : Z) :
    (∫ x, UnitAddTorus.mFourier (-k) (torusProjection x) * f (WithLp.toLp 2 x)) =
      (𝓕 f) (euclideanIntegerPoint k) := by
  rw [Real.fourier_eq']
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 X).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integer_character_eq_fourier_phase]
  rfl

/-- Normal lattice translates and summable Fourier samples imply Poisson summation. -/
theorem euclidean_poisson_of_summable_translates {f : E → ℂ} (hf : Continuous f)
    (hi : Integrable f)
    (hn : ∀ R : ℝ, 0 ≤ R → ∃ u : Z → ℝ, Summable u ∧
      ∀ x : X, ‖x‖ ≤ R → ∀ k : Z,
        ‖f (WithLp.toLp 2 (x + integerPoint k))‖ ≤ u k)
    (hs : Summable (fun k : Z => (𝓕 f) (euclideanIntegerPoint k))) :
    (∑' k : Z, f (euclideanIntegerPoint k)) =
      ∑' k : Z, (𝓕 f) (euclideanIntegerPoint k) := by
  have ht : Continuous (WithLp.toLp 2 : X → E) :=
    (PiLp.homeomorph 2 (fun _ : ι => ℝ)).symm.continuous
  have hi' : Integrable (fun x : X => f (WithLp.toLp 2 x)) :=
    ((PiLp.volume_preserving_toLp ι).integrable_comp_emb
      (MeasurableEquiv.toLp 2 X).measurableEmbedding).mpr hi
  have hs' : Summable (fun k : Z => ∫ x,
      UnitAddTorus.mFourier (-k) (torusProjection x) * f (WithLp.toLp 2 x)) := by
    simpa only [integer_fourier_coefficient] using hs
  have h := poisson_of_summable_translates (hf.comp ht) hi' hn hs'
  simp only [Function.comp_def, integer_fourier_coefficient] at h
  simpa only [euclideanIntegerPoint] using h.symm

private def twist (f : E → ℂ) (a : E) (x : X) : ℂ :=
  Complex.exp ((2 * Real.pi * inner ℝ (WithLp.toLp 2 x) a : ℝ) * Complex.I) *
    f (WithLp.toLp 2 x)

private theorem twist_continuous (f : SchwartzMap E ℂ) (a : E) :
    Continuous (twist f a) := by
  unfold twist
  have ht : Continuous (WithLp.toLp 2 : X → E) :=
    (PiLp.homeomorph 2 (fun _ : ι => ℝ)).symm.continuous
  exact ((Complex.continuous_ofReal.comp (continuous_const.mul
    (ht.inner continuous_const))).mul continuous_const).cexp.mul (f.continuous.comp ht)

private theorem twist_norm (f : SchwartzMap E ℂ) (a : E) (x : X) :
    ‖twist f a x‖ = ‖f (WithLp.toLp 2 x)‖ := by
  simp [twist, Complex.norm_exp]

private theorem twist_integrable (f : SchwartzMap E ℂ) (a : E) :
    Integrable (twist f a) := by
  have hi : Integrable (fun x : X => f (WithLp.toLp 2 x)) :=
    ((PiLp.volume_preserving_toLp ι).integrable_comp_emb
      (MeasurableEquiv.toLp 2 X).measurableEmbedding).mpr f.integrable
  exact hi.mono (twist_continuous f a).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (twist_norm f a x).le))

private theorem twist_coefficient (f : SchwartzMap E ℂ) (a : E) (k : Z) :
    (∫ x, UnitAddTorus.mFourier (-k) (q x) * twist f a x) =
      (𝓕 f) (euclideanIntegerPoint k - a) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 X).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integer_character_eq_fourier_phase]
  simp only [twist, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [inner_sub_right]
  push_cast
  ring

/-- Twisted Poisson summation in arbitrary finite dimension, with all convergence
conditions discharged by Schwartz decay. -/
theorem schwartz_poisson_twisted (f : SchwartzMap E ℂ) (a : E) :
    (∑' k : Z, (𝓕 f) (euclideanIntegerPoint k - a)) =
      ∑' n : Z,
        Complex.exp ((2 * Real.pi * inner ℝ (euclideanIntegerPoint n) a : ℝ) * Complex.I) *
          f (euclideanIntegerPoint n) := by
  have hn : ∀ R : ℝ, 0 ≤ R → ∃ u : Z → ℝ, Summable u ∧
      ∀ x : X, ‖x‖ ≤ R → ∀ n : Z, ‖twist f a (x + ip n)‖ ≤ u n := by
    intro R hR
    obtain ⟨u, hu, hb⟩ := schwartz_summable_translates f R hR
    exact ⟨u, hu, fun x hx n => (twist_norm f a _).le.trans (hb x hx n)⟩
  have hs : Summable (fun k : Z => (𝓕 f) (euclideanIntegerPoint k - a)) := by
    simpa only [sub_eq_add_neg] using (summable_norm_integerPoint_add (𝓕 f) (-a)).of_norm
  have h := poisson_of_summable_translates (twist_continuous f a) (twist_integrable f a)
    hn (by simpa only [twist_coefficient] using hs)
  simp only [twist_coefficient] at h
  simpa only [twist, euclideanIntegerPoint, zero_add] using h

/-- The lattice sum of a Schwartz function equals the lattice sum of its Fourier transform. -/
theorem schwartz_poisson (f : SchwartzMap E ℂ) :
    (∑' n : Z, f (euclideanIntegerPoint n)) = ∑' n : Z, (𝓕 f) (euclideanIntegerPoint n) := by
  simpa only [sub_zero, inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul] using (schwartz_poisson_twisted f 0).symm

end GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
