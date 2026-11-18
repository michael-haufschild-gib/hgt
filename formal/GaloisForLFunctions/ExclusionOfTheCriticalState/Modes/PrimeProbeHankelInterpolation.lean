import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.SparseProbeShiftReadings
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fin.Tuple.Embedding
import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant
import GaloisForLFunctions.RHTower.Deninger.DeningerKroneckerFieldStage

/-!
# Interpolation by arbitrary translates at prime sample times

After erasing any set of samples of finite harmonic mass, each finite
family of distinct probe translates still interpolates arbitrary real
data on a suitable set of sample times. On primes this gives nonsingular
Hankel minors of every order beyond any prescribed finite collection of
failed readings.
-/

noncomputable section
open MeasureTheory Set Function
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations

/-- A Hankel minor with arbitrary row times and translate orders. -/
def probeHankelMinor {n : ℕ} (F : ℝ → ℝ) (r j : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => criticalProbeSample F (r i + j k)

/-- On every harmonic-divergent schedule there are distinct nodes giving a nonsingular minor
for any prescribed distinct translate orders. -/
theorem probeHankelMinor_exists {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hn : ¬ F =ᵐ[volume] 0) {ι : Type*} (a : ι ↪ ℕ)
    (ha : ¬ Summable fun i => (1:ℝ) / ((a i : ℝ)+1)) {n : ℕ} (j : Fin n ↪ ℕ) :
    ∃ r : Fin n ↪ ι, (probeHankelMinor F (a ∘ r) j).det ≠ 0 := by
  have hcols := (sampledProbeTranslates_linearIndependent hF hn a ha).comp j j.injective
  obtain ⟨r,hr⟩ := _root_.RHTower.exists_evaluation_minor_ne_zero_of_linearIndependent _ hcols
  change (probeHankelMinor F (a ∘ r) j).det ≠ 0 at hr
  have hi : Injective r := by
    intro u v h
    by_contra huv
    apply hr (Matrix.det_zero_of_row_eq huv ?_)
    exact congrArg (fun t => fun k => criticalProbeSample F (a t + j k)) h
  exact ⟨⟨r,hi⟩,hr⟩

/-- Surviving infinite rows admit exact interpolation after harmonic-summable erasures. -/
theorem erasedProbeHankel_interpolation {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hn : ¬ F =ᵐ[volume] 0) {ι : Type*} (a : ι ↪ ℕ)
    (ha : ¬ Summable fun i => (1:ℝ)/((a i:ℝ)+1))
    (B : Set ι) (hB : Summable fun i : B => (1:ℝ)/((a i.val:ℝ)+1))
    {n : ℕ} (j : Fin n ↪ ℕ) :
    ∃ r : Fin n ↪ ι, (∀ i, r i ∉ B) ∧ (probeHankelMinor F (a ∘ r) j).det ≠ 0 ∧
      ∀ v : Fin n → ℝ, ∃! c : Fin n → ℝ, (probeHankelMinor F (a ∘ r) j).mulVec c = v := by
  let e := (Embedding.subtype (· ∈ Bᶜ)).trans a
  have hd : ¬ Summable fun i : {t : ι // t ∉ B} => (1:ℝ)/((e i:ℝ)+1) := fun h =>
    ha ((summable_subtype_and_compl (s := B)).1 ⟨hB,h⟩)
  obtain ⟨u,hu⟩ := probeHankelMinor_exists hF hn e hd j
  let r := u.trans (Embedding.subtype (· ∈ Bᶜ))
  let M := probeHankelMinor F (a ∘ r) j
  have hm : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.mpr hu)
  refine ⟨r,fun i => (u i).property,hu,?_⟩
  intro v
  obtain ⟨c,hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hm v
  exact ⟨c,hc,fun y hy => Matrix.mulVec_injective_iff_isUnit.mpr hm (hy.trans hc.symm)⟩

/-- Prime rows outside any set of finite reciprocal mass interpolate every prescribed vector. -/
theorem primeProbeHankel_interpolation {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hn : ¬ F =ᵐ[volume] 0) (B : Set Nat.Primes)
    (hB : Summable fun q : B => (1:ℝ)/((q.val.val:ℝ)+1)) {n : ℕ} (j : Fin n ↪ ℕ) :
    ∃ r : Fin n ↪ Nat.Primes, (∀ i, r i ∉ B) ∧
      (probeHankelMinor F (fun i => (r i).val) j).det ≠ 0 ∧
      ∀ v : Fin n → ℝ, ∃! c : Fin n → ℝ,
        (probeHankelMinor F (fun i => (r i).val) j).mulVec c = v :=
  erasedProbeHankel_interpolation hF hn (Embedding.subtype _) primeProbe_reciprocal_diverges B hB j

/-- The restriction to surviving rows is incompatible with every lower-dimensional
factorization, even if the proposed row and column features are entirely arbitrary. -/
theorem primeProbeHankel_no_low_rank_model {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hn : ¬ F =ᵐ[volume] 0) (B : Set Nat.Primes)
    (hB : Summable fun q : B => (1:ℝ)/((q.val.val:ℝ)+1)) {n d : ℕ} (hd : d<n) (j : Fin n ↪ ℕ)
    (L : Nat.Primes → Fin d → ℝ) (R : Fin d → Fin n → ℝ) :
    ∃ q ∉ B, ∃ i, criticalProbeSample F (q.val+j i) ≠ ∑ t, L q t * R t i := by
  by_contra! h
  obtain ⟨r,hr,hM,_⟩ := primeProbeHankel_interpolation hF hn B hB j
  let M := probeHankelMinor F (fun i => (r i).val) j
  let A : Matrix (Fin n) (Fin d) ℝ := fun i t => L (r i) t
  let Rmat : Matrix (Fin d) (Fin n) ℝ := R
  have he : M = A * Rmat := Matrix.ext fun i k => h (r i) (hr i) k
  have hunit := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.mpr hM)
  have hfull := Matrix.rank_of_isUnit M hunit
  have hle := (Matrix.rank_mul_le_left A Rmat).trans (Matrix.rank_le_card_width A)
  rw [← he,hfull] at hle
  exact (not_le_of_gt hd) (by simpa only [Fintype.card_fin] using hle)

/-- Every exponential test profile gives an exact Cauchy minor at arbitrary sample times. -/
theorem exponentialProbeHankel_determinant {n : ℕ} {t : ℝ} (ht : -5 < t)
    (r j : Fin n → ℕ) :
    (probeHankelMinor (probe t) r j).det * (∏ i, ∏ k, (t+5+(r i:ℝ)+(j k:ℝ))) =
      ∏ i, ∏ k ∈ Finset.Ioi i, (((r i:ℝ)-r k)*((j i:ℝ)-j k)) := by
  let x := fun i => t+5+(r i:ℝ)
  let y := fun i => (j i:ℝ)
  have hpos (i k : Fin n) : 0 < x i + y k := by
    dsimp only [x,y]
    linarith [Nat.cast_nonneg (α := ℝ) (r i),Nat.cast_nonneg (α := ℝ) (j k)]
  have he : probeHankelMinor (probe t) r j = HTGeometry.cauchyMatrix x y := by
    ext i k
    change (∫ u, probe t u * Real.exp ((5+((r i+j k:ℕ):ℝ))*u)) = (x i+y k)⁻¹
    have hsum : t+(5+((r i+j k:ℕ):ℝ)) = x i+y k := by dsimp [x,y]; push_cast; ring
    rw [integral_probe_mul_exp (by rw [hsum]; exact hpos i k), hsum, one_div]
  rw [he,HTGeometry.det_cauchyMatrix x y (fun i k => (hpos i k).ne')]
  simp only [x,y,add_sub_add_left_eq_sub]

/-- For an exponential profile every increasing minor is strictly positive, including arbitrary prime rows. -/
theorem exponentialProbeHankel_strictly_positive {n : ℕ} {t : ℝ} (ht : -5 < t)
    {r j : Fin n → ℕ} (hr : StrictMono r) (hj : StrictMono j) :
    0 < (probeHankelMinor (probe t) r j).det := by
  have hn : 0 < ∏ i, ∏ k ∈ Finset.Ioi i, (((r i:ℝ)-r k)*((j i:ℝ)-j k)) := by
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun k hk => ?_
    have h := Finset.mem_Ioi.mp hk
    exact mul_pos_of_neg_of_neg (sub_neg.mpr (by exact_mod_cast hr h))
      (sub_neg.mpr (by exact_mod_cast hj h))
  rw [← exponentialProbeHankel_determinant ht r j] at hn
  have hd : 0 < ∏ i, ∏ k, (t+5+(r i:ℝ)+(j k:ℝ)) := by
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun k _ => ?_
    linarith [Nat.cast_nonneg (α := ℝ) (r i),Nat.cast_nonneg (α := ℝ) (j k)]
  exact pos_of_mul_pos_left hn hd.le

/-- Arbitrarily ordered distinct nodes yield invertible matrices for the explicit probe family. -/
theorem exponentialProbeHankel_isUnit {n : ℕ} {t : ℝ} (ht : -5 < t) (r j : Fin n ↪ ℕ) :
    IsUnit (probeHankelMinor (probe t) r j) := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_iff_ne_zero.mpr
  intro h
  have he := exponentialProbeHankel_determinant ht r j
  rw [h,zero_mul] at he
  apply (Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun k hk =>
    mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast r.injective.ne (Finset.mem_Ioi.mp hk).ne))
      (sub_ne_zero.mpr (by exact_mod_cast j.injective.ne (Finset.mem_Ioi.mp hk).ne))) he.symm

/-- A nonzero filter with n distinct translates of the exponential profile cannot have n distinct zeros. -/
theorem exponentialProbeHankel_zero_bound {n : ℕ} {t : ℝ} (ht : -5 < t) (j : Fin n ↪ ℕ)
    (c : Fin n → ℝ) (hc : c ≠ 0) :
    ¬ ∃ r : Fin n ↪ ℕ, ∀ i, ∑ k, criticalProbeSample (probe t) (r i+j k)*c k = 0 := by
  rintro ⟨r,hr⟩
  let M := probeHankelMinor (probe t) r j
  have he : M.mulVec c = M.mulVec 0 := by rw [Matrix.mulVec_zero]; exact funext hr
  exact hc (Matrix.mulVec_injective_iff_isUnit.mpr (exponentialProbeHankel_isUnit ht r j) he)

/-- Any prescribed n-node zero set occurs for a unique filter with n+1 distinct translates
and unit reading at a chosen outside node. This attains the zero bound exactly. -/
theorem exponentialProbeHankel_prescribed_zeros {n : ℕ} {t : ℝ} (ht : -5 < t)
    (j : Fin (n+1) ↪ ℕ) (r : Fin n ↪ ℕ) (a : ℕ) (ha : a ∉ Set.range r) :
    let f := fun (c : Fin (n+1) → ℝ) (m : ℕ) =>
      ∑ k, criticalProbeSample (probe t) (m+j k)*c k
    ∃! c, f c a = 1 ∧ ∀ m, f c m = 0 ↔ m ∈ Set.range r := by
  intro f
  let e := Fin.Embedding.cons r ha
  let M := probeHankelMinor (probe t) e j
  let b : Fin (n+1) → ℝ := Fin.cons 1 (fun _ : Fin n => 0)
  have hM := exponentialProbeHankel_isUnit ht e j
  obtain ⟨c,hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hM b
  have h₁ : f c a = 1 := congrFun hc 0
  have h₀ (i : Fin n) : f c (r i) = 0 := congrFun hc i.succ
  have hne : c ≠ 0 := fun h => by simp [f,h] at h₁
  refine ⟨c,⟨h₁,fun m => ⟨fun hm => ?_,fun ⟨i,hi⟩ => hi ▸ h₀ i⟩⟩,?_⟩
  · by_contra hu
    apply exponentialProbeHankel_zero_bound ht j c hne
    exact ⟨Fin.Embedding.cons r hu, fun i => Fin.cases hm h₀ i⟩
  · intro d hd
    apply Matrix.mulVec_injective_iff_isUnit.mpr hM
    rw [hc]
    funext i
    exact Fin.cases hd.1 (fun k => (hd.2 (r k)).2 ⟨k,rfl⟩) i

#print axioms exponentialProbeHankel_prescribed_zeros
#print axioms exponentialProbeHankel_determinant
#print axioms exponentialProbeHankel_strictly_positive
#print axioms exponentialProbeHankel_isUnit
#print axioms exponentialProbeHankel_zero_bound
#print axioms probeHankelMinor_exists
#print axioms erasedProbeHankel_interpolation
#print axioms primeProbeHankel_interpolation
#print axioms primeProbeHankel_no_low_rank_model

end GaloisForLFunctions.ExclusionOfTheCriticalState
