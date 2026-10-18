import GaloisForLFunctions.BiScaleUncertainty.PrimeRawMomentRecovery
import GaloisForLFunctions.HTGeometry.InvarianceOfDomain

/-!
# Raw-measurement necessity and an exact decoder

Every fixed protocol with fewer literal observations than prime coefficients
has two distinct positive coefficient vectors with identical data. The proof
uses the corpus's unconditional invariance-of-domain theorem. Literal tests
include translated moments of every degree and the existing affine moments.

The explicit decoder forms signed 64-vertex contrasts, selects the least prime
with a nonzero diagonal, and recovers the coefficient vector with one common sign.
-/

open scoped BigOperators
open Finset Set
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.PrimeRaw
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
open GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem observation_dimension {m n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → Fin m → ℝ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hne : U.Nonempty) (hF : ContinuousOn F U) (hinj : Set.InjOn F U) :
    n ≤ m := by
  by_contra hn
  have hmn : m < n := Nat.lt_of_not_ge hn
  let pad : (Fin m → ℝ) → EuclideanSpace ℝ (Fin n) := fun y =>
    WithLp.toLp 2 (fun i => if h : i.val < m then y ⟨i.val,h⟩ else 0)
  have hpad : Function.Injective pad := by
    intro x y he
    funext i
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z ⟨i.val, lt_trans i.isLt hmn⟩) he
    simpa [pad] using hi
  have hpcont : Continuous pad := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    apply continuous_pi
    intro i
    by_cases hi : i.val < m
    · simpa only [dif_pos hi] using (continuous_apply (⟨i.val,hi⟩ : Fin m))
    · simp only [dif_neg hi]
      exact continuous_const
  have hG : IsOpen ((pad ∘ F) '' U) :=
    GaloisForLFunctions.invariance_of_domain_open_map (pad ∘ F) U hU
      (hpcont.comp_continuousOn hF) (fun x hx y hy he => hinj hx hy (hpad he))
  let i : Fin n := ⟨m,hmn⟩
  let H : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    LinearMap.ker (PiLp.projₗ (𝕜 := ℝ) (p := 2) (β := fun _ : Fin n => ℝ) i)
  have hsub : (pad ∘ F) '' U ⊆ (H : Set (EuclideanSpace ℝ (Fin n))) := by
    rintro z ⟨x,hx,rfl⟩
    change (pad (F x)) i = 0
    simp [pad, i]
  obtain ⟨x,hx⟩ := hne
  have htop : H = ⊤ := Submodule.eq_top_of_nonempty_interior' H
    ⟨pad (F x), (hG.subset_interior_iff.mpr hsub) ⟨x,hx,rfl⟩⟩
  have hmem : (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))) ∈ H := by
    rw [htop]
    trivial
  change (1 : ℝ) = 0 at hmem
  exact one_ne_zero hmem

/-- Extend Euclidean prime coordinates to actual natural-indexed sieve coefficients. -/
def vectorCoefficients (N : ℕ)
    (x : EuclideanSpace ℝ (Fin (Fintype.card (oddPrimeModes N)))) (p : ℕ) : ℝ :=
  if hp : p ∈ oddPrimeModes N then x (Fintype.equivFin (oddPrimeModes N) ⟨p,hp⟩) else 0

/-- The extension preserves every admissible coefficient. -/
theorem vectorCoefficients_at (N : ℕ)
    (x : EuclideanSpace ℝ (Fin (Fintype.card (oddPrimeModes N)))) (p : oddPrimeModes N) :
    vectorCoefficients N x p = x (Fintype.equivFin (oddPrimeModes N) p) := by
  simp [vectorCoefficients, p.property]

/-- One actual factorial-period mean of finitely many affine signal evaluations. -/
structure LiteralTest where
  degree : ℕ
  multiplier : Fin degree → ℕ
  shift : Fin degree → ℕ

/-- Evaluate a literal test on the actual prime-family sieve signal. -/
def literalObservation (N : ℕ) (a : ℕ → ℝ) (t : LiteralTest) : ℝ :=
  (∑ n ∈ Finset.range N.factorial, ∏ i : Fin t.degree,
    sieveSeq N (primeFamilyWeight N a) (t.multiplier i*n+t.shift i))/(N.factorial : ℝ)

private theorem literalObservation_continuous (N : ℕ) (t : LiteralTest) :
    Continuous (fun x : EuclideanSpace ℝ (Fin (Fintype.card (oddPrimeModes N))) =>
      literalObservation N (vectorCoefficients N x) t) := by
  unfold literalObservation sieveSeq primeFamilyWeight
  simp only [vectorCoefficients_at]
  fun_prop

/-- Fewer than M fixed observations force a collision between distinct positive M-mode vectors. -/
theorem underdetermined_collision (N m : ℕ) (tests : Fin m → LiteralTest) :
    Fintype.card (oddPrimeModes N) ≤ m ∨
      ∃ a b : ℕ → ℝ,
        (∀ p : oddPrimeModes N, 0 < a p ∧ 0 < b p) ∧
        (∃ p : oddPrimeModes N, a p ≠ b p) ∧
        (∀ j : Fin m, literalObservation N a (tests j) = literalObservation N b (tests j)) := by
  by_cases hdim : Fintype.card (oddPrimeModes N) ≤ m
  · exact Or.inl hdim
  right
  by_contra hno
  let E := EuclideanSpace ℝ (Fin (Fintype.card (oddPrimeModes N)))
  let U : Set E := {x | ∀ i, 0 < x i}
  let F : E → Fin m → ℝ := fun x j => literalObservation N (vectorCoefficients N x) (tests j)
  have hU : IsOpen U := by
    dsimp only [U]
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin (Fintype.card (oddPrimeModes N)) => ℝ) i)
  have hne : U.Nonempty := ⟨WithLp.toLp 2 (fun _ => 1), by intro i; norm_num⟩
  have hF : ContinuousOn F U := by
    apply Continuous.continuousOn
    apply continuous_pi
    exact fun j => literalObservation_continuous N (tests j)
  have hinj : Set.InjOn F U := by
    intro x hx y hy he
    have hp (p : oddPrimeModes N) : vectorCoefficients N x p = vectorCoefficients N y p := by
      by_contra hp
      apply hno
      refine ⟨vectorCoefficients N x, vectorCoefficients N y, ?_, ⟨p,hp⟩, ?_⟩
      · intro q
        rw [vectorCoefficients_at, vectorCoefficients_at]
        exact ⟨hx _, hy _⟩
      · intro j
        exact congrFun he j
    ext i
    have hh := hp ((Fintype.equivFin (oddPrimeModes N)).symm i)
    simpa only [vectorCoefficients_at, Equiv.apply_symm_apply] using hh
  exact hdim (observation_dimension F U hU hne hF hinj)

/-- Encode an ordinary translated-moment observation as a literal test. -/
def translatedTest {m : ℕ} (h : Fin m → ℕ) : LiteralTest := ⟨m, fun _ => 1, h⟩

/-- The literal test is exactly the existing translated moment. -/
theorem literal_translated (N : ℕ) (a : ℕ → ℝ) {m : ℕ} (h : Fin m → ℕ) :
    literalObservation N a (translatedTest h) =
      translatedMoment N (primeFamilyWeight N a) h := by
  change (∑ n ∈ Finset.range N.factorial, ∏ i : Fin m,
    sieveSeq N (primeFamilyWeight N a) (1*n+h i))/(N.factorial : ℝ) = _
  simp only [one_mul, translatedMoment]

/-- Encode the existing two-factor affine observation as a literal test. -/
def affineTest (r s : ℕ) : LiteralTest := ⟨2, ![1,r], ![0,s]⟩

/-- The literal test is exactly the existing affine moment. -/
theorem literal_affine (N : ℕ) (a : ℕ → ℝ) (r s : ℕ) :
    literalObservation N a (affineTest r s) = affineMoment N (primeFamilyWeight N a) r s := by
  change (∑ n ∈ Finset.range N.factorial, ∏ i : Fin 2,
    sieveSeq N (primeFamilyWeight N a) (![1,r] i*n+![0,s] i))/(N.factorial : ℝ) = _
  simp [affineMoment, Fin.prod_univ_two]


/-- Inverse of the injective real cube map; only verified cubes are used in exact reconstruction. -/
def inverseCube (x : ℝ) : ℝ := Function.invFun (fun t : ℝ => t^3) x

/-- The inverse cube returns every actual real coefficient product. -/
theorem inverseCube_cube (x : ℝ) : inverseCube (x^3) = x := by
  exact Function.leftInverse_invFun (show Odd (3 : ℕ) from ⟨1,rfl⟩).pow_injective x

/-- Prime indices with nonzero observed diagonal. -/
def anchorCandidates (N : ℕ) (R : oddPrimeModes N → oddPrimeModes N → ℝ) :
    Finset (oddPrimeModes N) := Finset.univ.filter (fun p => R p p ≠ 0)

/-- Select the least nonzero diagonal and divide recovered signed products by its positive magnitude. -/
def recover (N : ℕ) (R : oddPrimeModes N → oddPrimeModes N → ℝ) (p : oddPrimeModes N) : ℝ :=
  if h : (anchorCandidates N R).Nonempty then
    let r := (anchorCandidates N R).min' h
    inverseCube (R r p)/Real.sqrt (inverseCube (R r r))
  else 0

/-- The finite anchor procedure recovers every actual normalized readout matrix, including the zero vector. -/
theorem recover_actual (N : ℕ) (a : ℕ → ℝ) :
    (∀ p : oddPrimeModes N, recover N (normalizedReadout N a) p = a p) ∨
      (∀ p : oddPrimeModes N, recover N (normalizedReadout N a) p = -a p) := by
  by_cases h : (anchorCandidates N (normalizedReadout N a)).Nonempty
  · let r := (anchorCandidates N (normalizedReadout N a)).min' h
    have hr : normalizedReadout N a r r ≠ 0 :=
      (Finset.mem_filter.mp (Finset.min'_mem (anchorCandidates N (normalizedReadout N a)) h)).2
    have har : a r ≠ 0 := by
      intro hz
      apply hr
      rw [normalizedReadout_eq, hz]
      ring
    have hf (p : oddPrimeModes N) :
        recover N (normalizedReadout N a) p = (a r*a p)/|a r| := by
      simp only [recover, dif_pos h]
      change inverseCube (normalizedReadout N a r p)/
        Real.sqrt (inverseCube (normalizedReadout N a r r)) = _
      rw [normalizedReadout_eq, normalizedReadout_eq, inverseCube_cube, inverseCube_cube]
      rw [← pow_two, Real.sqrt_sq_eq_abs]
    rcases lt_or_gt_of_ne har with hneg | hpos
    · right
      intro p
      rw [hf, abs_of_neg hneg]
      field_simp [har]
    · left
      intro p
      rw [hf, abs_of_pos hpos]
      field_simp [har]
  · left
    intro p
    have hp : a p = 0 := by
      by_contra hp
      apply h
      refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [normalizedReadout_eq]
      exact pow_ne_zero 3 (mul_ne_zero hp hp)
    simp [recover, h, hp]

/-- An explicit decoder using only the stated raw observation array. -/
def decodeRaw (N : ℕ)
    (data : oddPrimeModes N → oddPrimeModes N → (Fin 6 → Fin 2) → ℝ)
    (p : oddPrimeModes N) : ℝ :=
  recover N (fun r s => (∑ v : Fin 6 → Fin 2, cubeSign v*data r s v)/pairScale N r s) p

/-- The raw-data decoder returns the entire actual coefficient vector up to common sign. -/
theorem decodeRaw_actual (N : ℕ) (a : ℕ → ℝ) :
    (∀ p : oddPrimeModes N, decodeRaw N (rawObservation N a) p = a p) ∨
      (∀ p : oddPrimeModes N, decodeRaw N (rawObservation N a) p = -a p) := by
  change (∀ p, recover N (normalizedReadout N a) p = a p) ∨
    (∀ p, recover N (normalizedReadout N a) p = -a p)
  exact recover_actual N a


end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.PrimeRaw
