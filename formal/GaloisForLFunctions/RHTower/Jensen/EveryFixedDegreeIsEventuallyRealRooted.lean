import GaloisForLFunctions.RHTower.XiJensenHermiteLimit
import GaloisForLFunctions.HTGeometry.HermiteSignChanges

/-!+# Eventual real-rootedness at every fixed Xi Jensen degree

The actual normalized Jensen polynomials converge to Hermite polynomials.
Their finitely many separated sign changes persist, forcing the full number
of real roots. Undoing the affine normalization gives the actual Xi family.
-/

open Polynomial Finset Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SignAlternation
noncomputable section
namespace RHTower

private theorem splits_of_separated_sign_changes (P : ℝ[X]) (Z : Finset ℝ)
    {ε : ℝ} (hε : 0 < ε) (hdeg : P.natDegree ≤ Z.card)
    (hsign : ∀ z ∈ Z, P.eval (z - ε) * P.eval (z + ε) < 0)
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * ε < |z - w|) : P.Splits := by
  classical
  by_cases hP : P = 0
  · simp only [hP, splits_zero]
  have hroot : ∀ z ∈ Z, ∃ r ∈ Set.Ioo (z - ε) (z + ε), P.IsRoot r :=
    fun z hz => exists_root_of_sign_change (by linarith) (hsign z hz)
  choose r hr hPr using hroot
  let f : ℝ → ℝ := fun z => if hz : z ∈ Z then r z hz else 0
  have hf (z : ℝ) (hz : z ∈ Z) : f z = r z hz := dif_pos hz
  have hinj : Set.InjOn f Z := by
    intro z hz w hw heq
    by_contra hne
    have hzr := hr z hz
    have hwr := hr w hw
    have he : r z hz = r w hw := by simpa only [hf z hz, hf w hw] using heq
    have hab : |z - w| < 2 * ε := by
      rw [abs_lt]
      constructor <;> linarith only [hzr.1, hzr.2, hwr.1, hwr.2, he]
    exact (not_lt_of_ge hab.le) (hsep z hz w hw hne)
  have hcard : Z.card ≤ P.roots.toFinset.card :=
    Finset.card_le_card_of_injOn (f := f)
      (fun z hz => by
        rw [Multiset.mem_toFinset, mem_roots hP, hf z hz]
        exact hPr z hz) hinj
  have h1 := Multiset.toFinset_card_le P.roots
  have h2 := Polynomial.card_roots' P
  rw [splits_iff_card_roots]
  omega

private theorem eventually_finset {α : Type*} (S : Finset α) (P : ℕ → α → Prop)
    (h : ∀ a ∈ S, ∀ᶠ n in atTop, P n a) :
    ∀ᶠ n in atTop, ∀ a ∈ S, P n a := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    filter_upwards [h a (mem_insert_self _ _),
      ih (fun b hb => h b (mem_insert_of_mem hb))] with n hn hS
    intro b hb
    rcases mem_insert.mp hb with rfl | hb
    · exact hn
    · exact hS b hb

/-- A harmless real dilation matches the separated forward-heat sign intervals. -/
private def heatScaledJensen (n d : ℕ) : ℝ[X] :=
  C (Real.sqrt 2 ^ d) *
    (xiJensenHermitePolynomial n d).comp (C ((Real.sqrt 2)⁻¹) * X)

private theorem heatScaledJensen_degree (n d : ℕ) :
    (heatScaledJensen n d).natDegree ≤ d := by
  refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
  exact (Nat.mul_le_mul (natDegree_xiJensenHermitePolynomial_le n d)
    (by simpa only [natDegree_X] using
      natDegree_C_mul_le ((Real.sqrt 2)⁻¹) (X : ℝ[X]))).trans_eq (Nat.mul_one d)

private theorem heatScaledJensen_eval_tendsto (d : ℕ) (x : ℝ) :
    Tendsto (fun n => (heatScaledJensen n d).eval x) atTop (𝓝 (heatPoly d x)) := by
  rw [eval_heatPoly_eq]
  have h := (tendsto_xiJensenHermitePolynomial_eval d (x / Real.sqrt 2)).const_mul
    (Real.sqrt 2 ^ d)
  simpa only [heatScaledJensen, eval_mul, eval_C, eval_comp, eval_X,
    inv_mul_eq_div, realHermite] using h

/-- Every fixed normalized Xi Jensen degree eventually splits over the reals. -/
theorem eventually_splits_xiJensenHermitePolynomial (d : ℕ) :
    ∀ᶠ n in atTop, (xiJensenHermitePolynomial n d).Splits := by
  obtain ⟨Z, hZ, ε, hε, hsign, hsep⟩ := exists_heatPoly_sign_changes d
  have he : ∀ z ∈ Z, ∀ᶠ n in atTop,
      (heatScaledJensen n d).eval (z - ε) *
        (heatScaledJensen n d).eval (z + ε) < 0 := by
    intro z hz
    exact ((heatScaledJensen_eval_tendsto d (z - ε)).mul
      (heatScaledJensen_eval_tendsto d (z + ε))).eventually_lt_const (hsign z hz)
  filter_upwards [eventually_finset Z _ he] with n hn
  have hs := splits_of_separated_sign_changes (heatScaledJensen n d) Z hε
    (by simpa only [hZ] using heatScaledJensen_degree n d) hn hsep
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hcomp := (splits_mul_iff_right
    (C_ne_zero.mpr (pow_ne_zero d hsqrt)) (splits_C _)).mp hs
  exact (splits_iff_comp_splits_of_natDegree_eq_one
    (by rw [natDegree_C_mul (inv_ne_zero hsqrt), natDegree_X])).mpr hcomp

/-- Actual Xi Jensen polynomials of every fixed degree are eventually real-rooted. -/
theorem eventually_splits_xiJensenPoly (d : ℕ) :
    ∀ᶠ n in atTop, (jensenPoly xiJensenCoeff d n).Splits := by
  filter_upwards [eventually_splits_xiJensenHermitePolynomial d] with n hn
  have hγ := (xiJensenCoeff_pos n).ne'
  have hδ := (xiJensenDelta_pos n).ne'
  have hA := (xiJensenScale_pos n).ne'
  have hcomp := (splits_mul_iff_right
    (C_ne_zero.mpr (inv_ne_zero (mul_ne_zero hγ (pow_ne_zero d hδ))))
    (splits_C _)).mp hn
  apply (splits_iff_comp_splits_of_natDegree_eq_one ?_).mpr hcomp
  rw [natDegree_C_mul (inv_ne_zero hA),
    natDegree_sub_eq_left_of_natDegree_lt (by
      simpa only [natDegree_one, natDegree_C_mul hδ, natDegree_X] using Nat.zero_lt_one),
    natDegree_C_mul hδ, natDegree_X]

end RHTower

#print axioms RHTower.eventually_splits_xiJensenHermitePolynomial
#print axioms RHTower.eventually_splits_xiJensenPoly
