import GaloisForLFunctions.HTGeometry.PolynomialTorsionLanguageDefectLimit
import GaloisForLFunctions.HTGeometry.FinitePiProductSummability
import GaloisForLFunctions.HTGeometry.MagnitudeWeightMassPolynomial
import GaloisForLFunctions.HTGeometry.PolynomialPhaseLockAssembly
import GaloisForLFunctions.HTGeometry.PolynomialPowerExplicitConfinement
import GaloisForLFunctions.HTGeometry.PolynomialTaylorProuhetPhaseLock
import GaloisForLFunctions.HTGeometry.FormalMahlerIntegerNormalization
import Mathlib.LinearAlgebra.Lagrange

/-!
# Gaussian torsion-language tail lock

At the quadratic Taylor scale the dominant ADE face is not confined to a fixed finite
offset window.  Its complete offset lattice is nevertheless absolutely summable: a grouped
weight has only polynomial growth in the offsets, while the exact residual valuation is a
positive Gaussian quadratic form.  This file develops the two analytic exactification tools
which are special to that critical scale:

* exact expansion of a translated quadratic lattice energy;
* domination of a max-polynomial constrained Gaussian by the coordinatewise ambient Gaussian;
* vanishing of the corresponding finite-box tails;
* approximate finite Fourier inversion.  Unlike the finite-face zero theorem, this last result
  retains a uniform error `epsilon`; it is the step which permits the window radius to tend to
  infinity only after torsion recurrence has exposed a chosen Fourier coefficient.

No bounded-confinement assertion is made: offsets of every fixed size remain on the quadratic
face.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open Filter Finset MvPolynomial Polynomial PowerSeries Topology

noncomputable section

/-! ## Exact quadratic offset energy -/

/-- The largest absolute coordinate of an integer lattice point, measured in `ℕ`. -/
def integerLatticeMaxNatAbs {ι : Type*} [Fintype ι] (z : ι → ℤ) : ℕ :=
  Finset.univ.sup fun i => (z i).natAbs

/-- Quadratic energy of an integer offset tuple. -/
def gaussianOffsetEnergy {ι : Type*} [Fintype ι] (z : ι → ℤ) : ℝ :=
  ∑ i, (z i : ℝ) ^ 2

/-- Translating every coordinate by the same real center splits the quadratic energy into its
center, source-sum, and transverse-offset terms. -/
theorem sum_sq_add_eq_center_source_offset
    {ι : Type*} [Fintype ι] (q : ℝ) (z : ι → ℤ) :
    (∑ i, (q + (z i : ℝ)) ^ 2) =
      (Fintype.card ι : ℝ) * q ^ 2 +
        2 * q * (∑ i, (z i : ℝ)) + gaussianOffsetEnergy z := by
  simp only [gaussianOffsetEnergy]
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (∑ i, 2 * q * (z i : ℝ)) =
      2 * q * ∑ i, (z i : ℝ) by
    rw [Finset.mul_sum]]

/-- Exact quadratic expansion for a bounded multiplicity pattern. -/
theorem polynomialPatternPowerValuation_two
    {M D : ℕ} (p : Fin M → Fin (D + 1)) (t : ℝ)
    (hcount : (∑ r, (p r : ℕ)) = D) :
    polynomialPatternPowerValuation 2 p t =
      (D : ℝ) * t ^ 2 +
        2 * t * (polynomialPatternMoment p 1 : ℝ) +
          (polynomialPatternMoment p 2 : ℝ) := by
  rw [polynomialPatternPowerValuation]
  simp_rw [Real.rpow_two, add_sq, mul_add, Finset.sum_add_distrib]
  have hcountR : (∑ x, ((p x : ℕ) : ℝ)) = D := by
    exact_mod_cast hcount
  have hm1 : (∑ x, ((p x : ℕ) : ℝ) * (x : ℝ)) =
      (polynomialPatternMoment p 1 : ℝ) := by
    rw [polynomialPatternMoment]
    push_cast
    simp only [pow_one]
  have hm2 : (∑ x, ((p x : ℕ) : ℝ) * (x : ℝ) ^ 2) =
      (polynomialPatternMoment p 2 : ℝ) := by
    rw [polynomialPatternMoment]
    push_cast
    rfl
  have hfirst : (∑ x, ((p x : ℕ) : ℝ) * t ^ 2) = (D : ℝ) * t ^ 2 := by
    rw [← Finset.sum_mul, hcountR]
  have hmiddle : (∑ x, ((p x : ℕ) : ℝ) * (2 * t * (x : ℝ))) =
      2 * t * (polynomialPatternMoment p 1 : ℝ) := by
    rw [← hm1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hfirst, hmiddle, hm2]

/-- Equal count and equal source sum make the quadratic valuation difference independent of the
translated center. -/
theorem polynomialPatternPowerValuation_two_sub_of_moment_one_eq
    {M D : ℕ} (p r : Fin M → Fin (D + 1)) (t : ℝ)
    (hpcount : (∑ j, (p j : ℕ)) = D)
    (hrcount : (∑ j, (r j : ℕ)) = D)
    (hmoment : polynomialPatternMoment p 1 = polynomialPatternMoment r 1) :
    polynomialPatternPowerValuation 2 p t -
        polynomialPatternPowerValuation 2 r t =
      (polynomialPatternMoment p 2 : ℝ) -
        (polynomialPatternMoment r 2 : ℝ) := by
  rw [polynomialPatternPowerValuation_two p t hpcount,
    polynomialPatternPowerValuation_two r t hrcount, hmoment]
  ring

/-- At the Gaussian exponent, increasing the source sum produces an eventual linear valuation
gap.  This is the critical-scale replacement for the `beta > 2` source-gap lemma. -/
theorem eventually_polynomialPatternPower_two_gap_of_sourceSum_lt
    {M D : ℕ} (p₀ p : Fin M → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hsource : polynomialPatternSourceSum p₀ < polynomialPatternSourceSum p) :
    ∀ᶠ t : ℝ in atTop,
      t ≤ polynomialPatternPowerValuation 2 p t -
        polynomialPatternPowerValuation 2 p₀ t := by
  have hm1Nat : polynomialPatternMoment p₀ 1 < polynomialPatternMoment p 1 := by
    rw [polynomialPatternMoment_one, polynomialPatternMoment_one]
    simpa [polynomialPatternSourceSum] using hsource
  have hm1 : (1 : ℝ) ≤
      (polynomialPatternMoment p 1 : ℝ) -
        (polynomialPatternMoment p₀ 1 : ℝ) := by
    have hm1cast : (polynomialPatternMoment p₀ 1 : ℝ) + 1 ≤
        (polynomialPatternMoment p 1 : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hm1Nat)
    linarith
  let b : ℝ := (polynomialPatternMoment p 2 : ℝ) -
    (polynomialPatternMoment p₀ 2 : ℝ)
  filter_upwards [eventually_ge_atTop |b|] with t ht
  rw [polynomialPatternPowerValuation_two p t hcount,
    polynomialPatternPowerValuation_two p₀ t hcount₀]
  have ht0 : 0 ≤ t := (abs_nonneg b).trans ht
  have hb : -|b| ≤ b := neg_abs_le b
  dsimp [b] at ht hb ⊢
  nlinarith

/-- On a finite family, the Gaussian source gap is uniform outside the least-source class. -/
theorem eventually_uniform_polynomialPatternPower_two_source_gap
    {M D : ℕ} (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty)
    (hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D)
    (p₀ : Fin M → Fin (D + 1))
    (hp₀ : p₀ ∈ polynomialPatternLeastSourceClass S hS) :
    ∀ᶠ t : ℝ in atTop, ∀ p ∈ S \ polynomialPatternLeastSourceClass S hS,
      t ≤ polynomialPatternPowerValuation 2 p t -
        polynomialPatternPowerValuation 2 p₀ t := by
  let T := S \ polynomialPatternLeastSourceClass S hS
  have hp₀S : p₀ ∈ S := polynomialPatternLeastSourceClass_subset S hS hp₀
  have hp₀source := sourceSum_eq_of_mem_polynomialPatternLeastSourceClass hp₀
  have hgap : ∀ p : ↥T, ∀ᶠ t : ℝ in atTop,
      t ≤ polynomialPatternPowerValuation 2 p.1 t -
        polynomialPatternPowerValuation 2 p₀ t := by
    intro p
    have hpS : p.1 ∈ S := (Finset.mem_sdiff.mp p.2).1
    have hpClass : p.1 ∉ polynomialPatternLeastSourceClass S hS :=
      (Finset.mem_sdiff.mp p.2).2
    have hsource : polynomialPatternSourceSum p₀ <
        polynomialPatternSourceSum p.1 := by
      rw [hp₀source]
      exact minimalSourceSum_lt_of_mem_not_class hS hpS hpClass
    exact eventually_polynomialPatternPower_two_gap_of_sourceSum_lt p₀ p.1
      (hcount p₀ hp₀S) (hcount p.1 hpS) hsource
  have hall : ∀ᶠ t : ℝ in atTop, ∀ p : ↥T,
      t ≤ polynomialPatternPowerValuation 2 p.1 t -
        polynomialPatternPowerValuation 2 p₀ t := eventually_all.mpr hgap
  filter_upwards [hall] with t ht
  intro p hp
  exact ht ⟨p, hp⟩

/-! ## Global Gaussian offset faces -/

/-- Integer offsets represented by the centered finite window `[-R,R]`. -/
def gaussianOffsetInterval (R : ℕ) : Finset ℤ :=
  Finset.Icc (-(R : ℤ)) (R : ℤ)

/-- Signed source sum of a finite multiplicity pattern on integer offsets. -/
def gaussianOffsetSource (a : ℤ →₀ ℕ) : ℤ :=
  a.sum fun r k => r * (k : ℤ)

/-- Quadratic energy of a finite multiplicity pattern on integer offsets. -/
def gaussianOffsetPatternEnergy (a : ℤ →₀ ℕ) : ℤ :=
  a.sum fun r k => r ^ 2 * (k : ℤ)

theorem gaussianOffsetPatternEnergy_nonneg (a : ℤ →₀ ℕ) :
    0 ≤ gaussianOffsetPatternEnergy a := by
  rw [gaussianOffsetPatternEnergy, Finsupp.sum]
  exact Finset.sum_nonneg fun r _hr => mul_nonneg (sq_nonneg r) (by positivity)

/-- Degree-`D`, signed-source-`S` Gaussian patterns supported in `[-R,R]`. -/
def gaussianOffsetFace (D : ℕ) (S : ℤ) (R : ℕ) : Finset (ℤ →₀ ℕ) :=
  ((gaussianOffsetInterval R).finsuppAntidiag D).filter fun a =>
    gaussianOffsetSource a = S

@[simp] theorem mem_gaussianOffsetFace
    {D : ℕ} {S : ℤ} {R : ℕ} {a : ℤ →₀ ℕ} :
    a ∈ gaussianOffsetFace D S R ↔
      (∑ r ∈ gaussianOffsetInterval R, a r) = D ∧
      a.support ⊆ gaussianOffsetInterval R ∧ gaussianOffsetSource a = S := by
  simp [gaussianOffsetFace, Finset.mem_finsuppAntidiag, and_assoc]

theorem gaussianOffsetFace_totalCount
    {D : ℕ} {S : ℤ} {R : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) :
    a.sum (fun _ k => k) = D := by
  obtain ⟨hcount, hsupp, _hsource⟩ := mem_gaussianOffsetFace.mp ha
  rw [Finsupp.sum_of_support_subset a hsupp (fun _ k => k) (by simp)]
  exact hcount

theorem gaussianOffsetFace_mono
    {D : ℕ} {S : ℤ} {R R' : ℕ} (hRR' : R ≤ R') :
    gaussianOffsetFace D S R ⊆ gaussianOffsetFace D S R' := by
  intro a ha
  obtain ⟨_hcount, hsupp, hsource⟩ := mem_gaussianOffsetFace.mp ha
  have hinterval : gaussianOffsetInterval R ⊆ gaussianOffsetInterval R' := by
    intro z hz
    simp only [gaussianOffsetInterval, Finset.mem_Icc] at hz ⊢
    constructor <;> omega
  have hsupp' : a.support ⊆ gaussianOffsetInterval R' := hsupp.trans hinterval
  have hcount' : (∑ r ∈ gaussianOffsetInterval R', a r) = D := by
    rw [← gaussianOffsetFace_totalCount ha,
      Finsupp.sum_of_support_subset a hsupp' (fun _ k => k) (by simp)]
  exact mem_gaussianOffsetFace.mpr ⟨hcount', hsupp', hsource⟩

/-- Canonical equivalence between a centered window index and its signed integer offset. -/
noncomputable def centeredIndexEquiv (R : ℕ) :
    Fin (2 * R + 1) ≃ ↥(gaussianOffsetInterval R) where
  toFun j := ⟨(j : ℤ) - (R : ℤ), by
    simp only [gaussianOffsetInterval, Finset.mem_Icc]
    have hj := j.isLt
    constructor <;> omega⟩
  invFun z := ⟨Int.toNat (z.1 + (R : ℤ)), by
    have hz := z.2
    simp only [gaussianOffsetInterval, Finset.mem_Icc] at hz
    have hnonneg : 0 ≤ z.1 + (R : ℤ) := by omega
    apply (Int.toNat_lt hnonneg).2
    omega⟩
  left_inv j := by
    apply Fin.ext
    simp only
    have heq : (j : ℤ) - (R : ℤ) + (R : ℤ) = (j : ℤ) := by ring
    rw [heq]
    simp
  right_inv z := by
    apply Subtype.ext
    simp only
    have hz := z.2
    simp only [gaussianOffsetInterval, Finset.mem_Icc] at hz
    have hnonneg : 0 ≤ z.1 + (R : ℤ) := by omega
    rw [Int.toNat_of_nonneg hnonneg]
    omega

/-- Window multiplicities of a global degree-`D` offset pattern. -/
noncomputable def gaussianOffsetPatternWindow
    {D : ℕ} (a : ℤ →₀ ℕ) (hcount : a.sum (fun _ k => k) = D) (R : ℕ) :
    Fin (2 * R + 1) → Fin (D + 1) := fun j =>
  ⟨a ((centeredIndexEquiv R j).1), by
    have hle : a ((centeredIndexEquiv R j).1) ≤ a.sum (fun _ k => k) := by
      classical
      rw [Finsupp.sum]
      by_cases hj : (centeredIndexEquiv R j).1 ∈ a.support
      · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
      · have hz : a ((centeredIndexEquiv R j).1) = 0 := by
          simpa [Finsupp.mem_support_iff] using hj
        simp [hz]
    rw [hcount] at hle
    omega⟩

theorem gaussianOffsetPatternWindow_count
    {D : ℕ} {S : ℤ} {R : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) :
    (∑ j, (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R j : ℕ)) = D := by
  let hcount := gaussianOffsetFace_totalCount ha
  have hsupp := (mem_gaussianOffsetFace.mp ha).2.1
  change (∑ j : Fin (2 * R + 1), a ((centeredIndexEquiv R j).1)) = D
  calc
    (∑ j : Fin (2 * R + 1), a ((centeredIndexEquiv R j).1)) =
        ∑ z : ↥(gaussianOffsetInterval R), a z.1 :=
      Equiv.sum_comp (centeredIndexEquiv R) (fun z => a z.1)
    _ = ∑ z ∈ gaussianOffsetInterval R, a z := by
      simpa using (Finset.sum_attach (gaussianOffsetInterval R) (fun z => a z))
    _ = a.sum (fun _ k => k) := by
      symm
      exact Finsupp.sum_of_support_subset a hsupp (fun _ k => k) (by simp)
    _ = D := hcount

/-- Reindexing a global offset pattern through its centered finite window preserves every
finitely-supported additive statistic.  This is the common exact constructor behind the count,
signed-source, and Gaussian-energy identities. -/
theorem sum_gaussianOffsetPatternWindow_eq_finsuppSum
    {D : ℕ} {S : ℤ} {R : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R)
    {α : Type*} [AddCommMonoid α]
    (f : ℤ → ℕ → α) (hzero : ∀ z, f z 0 = 0) :
    (∑ j : Fin (2 * R + 1),
      f ((centeredIndexEquiv R j).1)
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R j : ℕ)) =
      a.sum f := by
  have hsupp := (mem_gaussianOffsetFace.mp ha).2.1
  change (∑ j : Fin (2 * R + 1),
    f ((centeredIndexEquiv R j).1) (a ((centeredIndexEquiv R j).1))) = a.sum f
  calc
    (∑ j : Fin (2 * R + 1),
        f ((centeredIndexEquiv R j).1) (a ((centeredIndexEquiv R j).1))) =
        ∑ z : ↥(gaussianOffsetInterval R), f z.1 (a z.1) :=
      Equiv.sum_comp (centeredIndexEquiv R) (fun z => f z.1 (a z.1))
    _ = ∑ z ∈ gaussianOffsetInterval R, f z (a z) := by
      simp
    _ = a.sum f := by
      symm
      exact Finsupp.sum_of_support_subset a hsupp f (fun z _hz => hzero z)

/-- The ordinary nonnegative source sum in a centered window is the global signed source plus
the deterministic translation contribution `R * D`. -/
theorem gaussianOffsetPatternWindow_source
    {D : ℕ} {S : ℤ} {R : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) :
    ((polynomialPatternSourceSum
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R) : ℕ) : ℤ) -
        (R : ℤ) * (D : ℤ) = S := by
  have hcountInt :
      (∑ j : Fin (2 * R + 1),
        ((gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R j : ℕ) : ℤ)) =
        (D : ℤ) := by
    exact_mod_cast gaussianOffsetPatternWindow_count ha
  have hcenter :
      (∑ j : Fin (2 * R + 1),
        (((j : ℕ) : ℤ) - (R : ℤ)) *
          ((gaussianOffsetPatternWindow a
            (gaussianOffsetFace_totalCount ha) R j : ℕ) : ℤ)) =
        gaussianOffsetSource a := by
    simpa only [centeredIndexEquiv, gaussianOffsetSource] using
      (sum_gaussianOffsetPatternWindow_eq_finsuppSum
        (ha := ha) (f := fun z k => z * (k : ℤ)) (by simp))
  have hsource := (mem_gaussianOffsetFace.mp ha).2.2
  rw [polynomialPatternSourceSum]
  push_cast
  calc
    (∑ j : Fin (2 * R + 1),
        (j : ℤ) *
          ((gaussianOffsetPatternWindow a
            (gaussianOffsetFace_totalCount ha) R j : ℕ) : ℤ)) -
        (R : ℤ) * (D : ℤ) =
        ∑ j : Fin (2 * R + 1),
          (((j : ℕ) : ℤ) - (R : ℤ)) *
            ((gaussianOffsetPatternWindow a
              (gaussianOffsetFace_totalCount ha) R j : ℕ) : ℤ) := by
      rw [← hcountInt, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = gaussianOffsetSource a := hcenter
    _ = S := hsource

/-- The centered quadratic moment of every window representative is the intrinsic energy of its
global offset pattern.  In particular, it is unchanged under later enlargements of the window. -/
theorem gaussianOffsetPatternWindow_energy
    {D : ℕ} {S : ℤ} {R : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) :
    (∑ j : Fin (2 * R + 1),
      (((j : ℕ) : ℤ) - (R : ℤ)) ^ 2 *
        ((gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount ha) R j : ℕ) : ℤ)) =
      gaussianOffsetPatternEnergy a := by
  simpa only [centeredIndexEquiv, gaussianOffsetPatternEnergy] using
    (sum_gaussianOffsetPatternWindow_eq_finsuppSum
      (ha := ha) (f := fun z k => z ^ 2 * (k : ℤ)) (by simp))

/-- Signed offset corresponding to a nonnegative coordinate in a window centered at `K`. -/
def centeredNatOffset (K r : ℕ) : ℤ :=
  (r : ℤ) - (K : ℤ)

theorem centeredNatOffset_injective (K : ℕ) :
    Function.Injective (centeredNatOffset K) := by
  intro r s hrs
  simp only [centeredNatOffset] at hrs
  omega

/-- Intrinsic signed-offset pattern represented by an arbitrary bounded window pattern. -/
def gaussianOffsetPatternOfWindow
    {M D : ℕ} (K : ℕ) (p : Fin M → Fin (D + 1)) : ℤ →₀ ℕ :=
  Finsupp.mapDomain (centeredNatOffset K) (atomPatternKey p)

theorem gaussianOffsetPatternOfWindow_totalCount
    {M D K : ℕ} (p : Fin M → Fin (D + 1)) :
    (gaussianOffsetPatternOfWindow K p).sum (fun _ k => k) =
      ∑ r, (p r : ℕ) := by
  rw [gaussianOffsetPatternOfWindow,
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact atomPatternKey_count p

theorem gaussianOffsetPatternOfWindow_support_subset
    {M D K : ℕ} (p : Fin M → Fin (D + 1)) :
    (gaussianOffsetPatternOfWindow K p).support ⊆
      gaussianOffsetInterval (K + M) := by
  classical
  rw [gaussianOffsetPatternOfWindow,
    Finsupp.mapDomain_support_of_injective (centeredNatOffset_injective K)]
  intro z hz
  obtain ⟨r, hrSupport, rfl⟩ := Finset.mem_image.mp hz
  have hrne : atomPatternKey p r ≠ 0 := Finsupp.mem_support_iff.mp hrSupport
  have hrlt : r < M := by
    by_contra hnot
    rw [atomPatternKey_apply, dif_neg hnot] at hrne
    exact hrne rfl
  simp only [gaussianOffsetInterval, Finset.mem_Icc, centeredNatOffset]
  constructor <;> omega

/-- Every degree-`D` bounded pattern defines a member of one centered global Gaussian face. -/
theorem gaussianOffsetPatternOfWindow_mem_face
    {M D K : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) :
    gaussianOffsetPatternOfWindow K p ∈
      gaussianOffsetFace D
        (gaussianOffsetSource (gaussianOffsetPatternOfWindow K p)) (K + M) := by
  have hsupp := gaussianOffsetPatternOfWindow_support_subset (K := K) p
  apply mem_gaussianOffsetFace.mpr
  refine ⟨?_, hsupp, rfl⟩
  calc
    (∑ z ∈ gaussianOffsetInterval (K + M),
        gaussianOffsetPatternOfWindow K p z) =
        (gaussianOffsetPatternOfWindow K p).sum (fun _ k => k) := by
      symm
      exact Finsupp.sum_of_support_subset
        (gaussianOffsetPatternOfWindow K p) hsupp (fun _ k => k) (fun _ _ => rfl)
    _ = ∑ r, (p r : ℕ) := gaussianOffsetPatternOfWindow_totalCount p
    _ = D := hcount

/-- The signed source of a window pattern is its ordinary source sum with the deterministic
`D*K` translation removed. -/
theorem gaussianOffsetSource_patternOfWindow
    {M D K : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) :
    gaussianOffsetSource (gaussianOffsetPatternOfWindow K p) =
      (polynomialPatternSourceSum p : ℤ) - (K : ℤ) * (D : ℤ) := by
  have hweightedInt :
      (atomPatternKey p).sum (fun r k => (r : ℤ) * (k : ℤ)) =
        (polynomialPatternSourceSum p : ℤ) := by
    rw [polynomialPatternSourceSum]
    exact_mod_cast atomPatternKey_weightedSum p
  have hcountInt :
      (atomPatternKey p).sum (fun _ k => (k : ℤ)) = (D : ℤ) := by
    have hcountKey : (atomPatternKey p).sum (fun _ k => k) = D := by
      rw [atomPatternKey_count, hcount]
    exact_mod_cast hcountKey
  rw [gaussianOffsetSource, gaussianOffsetPatternOfWindow,
    Finsupp.sum_mapDomain_index (fun _ => by simp)
      (fun _ x y => by push_cast; ring)]
  calc
    (atomPatternKey p).sum
        (fun r k => centeredNatOffset K r * (k : ℤ)) =
        (atomPatternKey p).sum (fun r k => (r : ℤ) * (k : ℤ)) -
          (K : ℤ) * (atomPatternKey p).sum (fun _ k => (k : ℤ)) := by
      simp only [Finsupp.sum, centeredNatOffset]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = (polynomialPatternSourceSum p : ℤ) - (K : ℤ) * (D : ℤ) := by
      rw [hweightedInt, hcountInt]

/-- Intrinsic signed-offset pattern obtained directly from an ADE atom key at translation `q`. -/
def gaussianOffsetPatternOfKey (q : ℕ) (ν : ℕ →₀ ℕ) : ℤ →₀ ℕ :=
  Finsupp.mapDomain (centeredNatOffset q) ν

theorem gaussianOffsetPatternOfKey_totalCount (q : ℕ) (ν : ℕ →₀ ℕ) :
    (gaussianOffsetPatternOfKey q ν).sum (fun _ k => k) =
      ν.sum (fun _ k => k) := by
  rw [gaussianOffsetPatternOfKey,
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

theorem gaussianOffsetSource_patternOfKey_eq_sum (q : ℕ) (ν : ℕ →₀ ℕ) :
    gaussianOffsetSource (gaussianOffsetPatternOfKey q ν) =
      ν.sum fun i k => ((i : ℤ) - (q : ℤ)) * (k : ℤ) := by
  rw [gaussianOffsetSource, gaussianOffsetPatternOfKey,
    Finsupp.sum_mapDomain_index (fun _ => by simp)
      (fun _ x y => by push_cast; ring)]
  rfl

theorem gaussianOffsetSource_patternOfKey (q : ℕ) (ν : ℕ →₀ ℕ) :
    gaussianOffsetSource (gaussianOffsetPatternOfKey q ν) =
      (ν.sum (fun i k => i * k) : ℤ) -
        (q : ℤ) * (ν.sum (fun _ k => k) : ℤ) := by
  rw [gaussianOffsetSource_patternOfKey_eq_sum]
  have hweighted :
      ν.sum (fun i k => (i : ℤ) * (k : ℤ)) =
        (ν.sum (fun i k => i * k) : ℤ) := by
    exact_mod_cast rfl
  have hcount :
      ν.sum (fun _ k => (k : ℤ)) =
        (ν.sum (fun _ k => k) : ℤ) := by
    exact_mod_cast rfl
  rw [← hweighted, ← hcount]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

theorem gaussianOffsetPatternEnergy_patternOfKey (q : ℕ) (ν : ℕ →₀ ℕ) :
    gaussianOffsetPatternEnergy (gaussianOffsetPatternOfKey q ν) =
      ν.sum fun i k => ((i : ℤ) - (q : ℤ)) ^ 2 * (k : ℤ) := by
  rw [gaussianOffsetPatternEnergy, gaussianOffsetPatternOfKey,
    Finsupp.sum_mapDomain_index (fun _ => by simp)
      (fun _ x y => by push_cast; ring)]
  rfl

/-- Support-window predicate for an atom key translated about `q`. -/
def gaussianAtomInWindow (q R : ℕ) (ν : ℕ →₀ ℕ) : Prop :=
  ∀ i, ν i ≠ 0 → q - R ≤ i ∧ i ≤ q + R

theorem gaussianOffsetPatternOfKey_support_subset
    {q R : ℕ} {ν : ℕ →₀ ℕ} (hRq : R ≤ q)
    (hwindow : gaussianAtomInWindow q R ν) :
    (gaussianOffsetPatternOfKey q ν).support ⊆ gaussianOffsetInterval R := by
  classical
  rw [gaussianOffsetPatternOfKey,
    Finsupp.mapDomain_support_of_injective (centeredNatOffset_injective q)]
  intro z hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  have hi0 : ν i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hiWindow := hwindow i hi0
  simp only [gaussianOffsetInterval, Finset.mem_Icc, centeredNatOffset]
  constructor <;> omega

theorem gaussianAtomInWindow_of_patternOfKey_support_subset
    {q R : ℕ} {ν : ℕ →₀ ℕ} (hRq : R ≤ q)
    (hsupp : (gaussianOffsetPatternOfKey q ν).support ⊆
      gaussianOffsetInterval R) :
    gaussianAtomInWindow q R ν := by
  intro i hi
  have hoff : centeredNatOffset q i ∈
      (gaussianOffsetPatternOfKey q ν).support := by
    rw [Finsupp.mem_support_iff, gaussianOffsetPatternOfKey,
      Finsupp.mapDomain_apply (centeredNatOffset_injective q)]
    exact hi
  have hz := hsupp hoff
  simp only [gaussianOffsetInterval, Finset.mem_Icc, centeredNatOffset] at hz
  constructor <;> omega

theorem gaussianOffsetPatternOfKey_mem_face
    {D q R : ℕ} {S : ℤ} {ν : ℕ →₀ ℕ}
    (hcount : ν.sum (fun _ k => k) = D)
    (hsource : gaussianOffsetSource (gaussianOffsetPatternOfKey q ν) = S)
    (hRq : R ≤ q) (hwindow : gaussianAtomInWindow q R ν) :
    gaussianOffsetPatternOfKey q ν ∈ gaussianOffsetFace D S R := by
  have hsupp := gaussianOffsetPatternOfKey_support_subset hRq hwindow
  apply mem_gaussianOffsetFace.mpr
  refine ⟨?_, hsupp, hsource⟩
  calc
    (∑ z ∈ gaussianOffsetInterval R, gaussianOffsetPatternOfKey q ν z) =
        (gaussianOffsetPatternOfKey q ν).sum (fun _ k => k) := by
      symm
      exact Finsupp.sum_of_support_subset
        (gaussianOffsetPatternOfKey q ν) hsupp (fun _ k => k) (fun _ _ => rfl)
    _ = ν.sum (fun _ k => k) := gaussianOffsetPatternOfKey_totalCount q ν
    _ = D := hcount

/-- Exact quadratic valuation expansion for an atom key written in intrinsic signed offsets. -/
theorem atomValuation_gaussianOffsetPatternOfKey
    (B : ℝ) {D q : ℕ} {S : ℤ} {ν : ℕ →₀ ℕ}
    (hcount : ν.sum (fun _ k => k) = D)
    (hsource : gaussianOffsetSource (gaussianOffsetPatternOfKey q ν) = S) :
    atomValuation (fun i => B * (i : ℝ) ^ 2) ν =
      B * ((D : ℝ) * (q : ℝ) ^ 2 + 2 * (q : ℝ) * (S : ℝ) +
        (gaussianOffsetPatternEnergy (gaussianOffsetPatternOfKey q ν) : ℝ)) := by
  have hcountR : ν.sum (fun _ k => (k : ℝ)) = (D : ℝ) := by
    exact_mod_cast hcount
  have hsourceInt :
      ν.sum (fun i k => ((i : ℤ) - (q : ℤ)) * (k : ℤ)) = S := by
    rw [← gaussianOffsetSource_patternOfKey_eq_sum]
    exact hsource
  have hsourceR :
      ν.sum (fun i k => ((i : ℝ) - (q : ℝ)) * (k : ℝ)) = (S : ℝ) := by
    exact_mod_cast hsourceInt
  have henergyInt :
      ν.sum (fun i k => ((i : ℤ) - (q : ℤ)) ^ 2 * (k : ℤ)) =
        gaussianOffsetPatternEnergy (gaussianOffsetPatternOfKey q ν) := by
    exact (gaussianOffsetPatternEnergy_patternOfKey q ν).symm
  have henergyR :
      ν.sum (fun i k => ((i : ℝ) - (q : ℝ)) ^ 2 * (k : ℝ)) =
        (gaussianOffsetPatternEnergy (gaussianOffsetPatternOfKey q ν) : ℝ) := by
    exact_mod_cast henergyInt
  have hquad :
      ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ 2) =
        (D : ℝ) * (q : ℝ) ^ 2 + 2 * (q : ℝ) * (S : ℝ) +
          (gaussianOffsetPatternEnergy (gaussianOffsetPatternOfKey q ν) : ℝ) := by
    simp only [Finsupp.sum] at hcountR hsourceR henergyR ⊢
    calc
      ∑ i ∈ ν.support, (ν i : ℝ) * (i : ℝ) ^ 2 =
          ∑ i ∈ ν.support,
            ((q : ℝ) ^ 2 * (ν i : ℝ) +
              2 * (q : ℝ) * (((i : ℝ) - (q : ℝ)) * (ν i : ℝ)) +
              (((i : ℝ) - (q : ℝ)) ^ 2 * (ν i : ℝ))) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (q : ℝ) ^ 2 * (∑ i ∈ ν.support, (ν i : ℝ)) +
          2 * (q : ℝ) *
            (∑ i ∈ ν.support, ((i : ℝ) - (q : ℝ)) * (ν i : ℝ)) +
          ∑ i ∈ ν.support,
            ((i : ℝ) - (q : ℝ)) ^ 2 * (ν i : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.mul_sum, Finset.mul_sum]
      _ = (D : ℝ) * (q : ℝ) ^ 2 + 2 * (q : ℝ) * (S : ℝ) +
          (gaussianOffsetPatternEnergy (gaussianOffsetPatternOfKey q ν) : ℝ) := by
        rw [hcountR, hsourceR, henergyR]
        ring
  change ν.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ 2)) = _
  calc
    ν.sum (fun i k => (k : ℝ) * (B * (i : ℝ) ^ 2)) =
        B * ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ 2) := by
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = B * ((D : ℝ) * (q : ℝ) ^ 2 + 2 * (q : ℝ) * (S : ℝ) +
        (gaussianOffsetPatternEnergy (gaussianOffsetPatternOfKey q ν) : ℝ)) := by
      rw [hquad]

/-- Finite centered pattern face corresponding to the intrinsic signed-source face. -/
def gaussianPolynomialPatternFace (D : ℕ) (S : ℤ) (R : ℕ) :
    Finset (Fin (2 * R + 1) → Fin (D + 1)) :=
  (degreeDPolynomialPatterns (2 * R + 1) D).filter fun p =>
    (polynomialPatternSourceSum p : ℤ) - (R : ℤ) * (D : ℤ) = S

@[simp] theorem mem_gaussianPolynomialPatternFace
    {D : ℕ} {S : ℤ} {R : ℕ}
    {p : Fin (2 * R + 1) → Fin (D + 1)} :
    p ∈ gaussianPolynomialPatternFace D S R ↔
      (∑ r, (p r : ℕ)) = D ∧
        (polynomialPatternSourceSum p : ℤ) - (R : ℤ) * (D : ℤ) = S := by
  simp [gaussianPolynomialPatternFace, degreeDPolynomialPatterns]

theorem gaussianOffsetPatternOfWindow_support_subset_centered
    {D R : ℕ} (p : Fin (2 * R + 1) → Fin (D + 1)) :
    (gaussianOffsetPatternOfWindow R p).support ⊆ gaussianOffsetInterval R := by
  classical
  rw [gaussianOffsetPatternOfWindow,
    Finsupp.mapDomain_support_of_injective (centeredNatOffset_injective R)]
  intro z hz
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
  have hr0 : atomPatternKey p r ≠ 0 := Finsupp.mem_support_iff.mp hr
  have hrlt : r < 2 * R + 1 := by
    by_contra hnot
    rw [atomPatternKey_apply, dif_neg hnot] at hr0
    exact hr0 rfl
  simp only [gaussianOffsetInterval, Finset.mem_Icc, centeredNatOffset]
  constructor <;> omega

theorem gaussianOffsetPatternOfWindow_mem_face_centered
    {D R : ℕ} {S : ℤ} (p : Fin (2 * R + 1) → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hsource : (polynomialPatternSourceSum p : ℤ) -
      (R : ℤ) * (D : ℤ) = S) :
    gaussianOffsetPatternOfWindow R p ∈ gaussianOffsetFace D S R := by
  have hsupp := gaussianOffsetPatternOfWindow_support_subset_centered p
  apply mem_gaussianOffsetFace.mpr
  refine ⟨?_, hsupp, ?_⟩
  · calc
      (∑ z ∈ gaussianOffsetInterval R, gaussianOffsetPatternOfWindow R p z) =
          (gaussianOffsetPatternOfWindow R p).sum (fun _ k => k) := by
        symm
        exact Finsupp.sum_of_support_subset
          (gaussianOffsetPatternOfWindow R p) hsupp (fun _ k => k) (fun _ _ => rfl)
      _ = ∑ r, (p r : ℕ) := gaussianOffsetPatternOfWindow_totalCount p
      _ = D := hcount
  · rw [gaussianOffsetSource_patternOfWindow p hcount]
    exact hsource

theorem gaussianOffsetPatternWindow_patternOfWindow_eq
    {D R : ℕ} {S : ℤ} (p : Fin (2 * R + 1) → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hsource : (polynomialPatternSourceSum p : ℤ) -
      (R : ℤ) * (D : ℤ) = S) :
    gaussianOffsetPatternWindow (gaussianOffsetPatternOfWindow R p)
      (gaussianOffsetFace_totalCount
        (gaussianOffsetPatternOfWindow_mem_face_centered p hcount hsource)) R = p := by
  funext j
  apply Fin.ext
  change gaussianOffsetPatternOfWindow R p (centeredNatOffset R (j : ℕ)) = (p j : ℕ)
  rw [gaussianOffsetPatternOfWindow,
    Finsupp.mapDomain_apply (centeredNatOffset_injective R)]
  change atomPatternKey p (j : ℕ) = (p j : ℕ)
  rw [atomPatternKey_apply, dif_pos j.isLt]

/-- Centered quadratic energy of a finite window pattern. -/
def gaussianWindowPatternEnergy {D R : ℕ}
    (p : Fin (2 * R + 1) → Fin (D + 1)) : ℤ :=
  ∑ j : Fin (2 * R + 1),
    (((j : ℕ) : ℤ) - (R : ℤ)) ^ 2 * ((p j : ℕ) : ℤ)

theorem gaussianWindowPatternEnergy_eq_patternOfWindow
    {D R : ℕ} {S : ℤ} (p : Fin (2 * R + 1) → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hsource : (polynomialPatternSourceSum p : ℤ) -
      (R : ℤ) * (D : ℤ) = S) :
    gaussianWindowPatternEnergy p =
      gaussianOffsetPatternEnergy (gaussianOffsetPatternOfWindow R p) := by
  let ha := gaussianOffsetPatternOfWindow_mem_face_centered p hcount hsource
  have henergy := gaussianOffsetPatternWindow_energy ha
  rw [gaussianOffsetPatternWindow_patternOfWindow_eq p hcount hsource] at henergy
  exact henergy

theorem gaussianOffsetPatternWindow_mem_gaussianPolynomialPatternFace
    {D R : ℕ} {S : ℤ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) :
    gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R ∈
      gaussianPolynomialPatternFace D S R := by
  rw [mem_gaussianPolynomialPatternFace]
  exact ⟨gaussianOffsetPatternWindow_count ha,
    gaussianOffsetPatternWindow_source ha⟩

/-- Translation of a signed global offset pattern to nonnegative coefficient indices.  The
definition is independent of any finite window used to display the pattern. -/
def gaussianOffsetShiftedKey (q : ℕ) (a : ℤ →₀ ℕ) : ℕ →₀ ℕ :=
  a.support.sum fun z =>
    Finsupp.single (Int.toNat ((q : ℤ) + z)) (a z)

theorem gaussianOffsetShiftedKey_eq_mapDomain (q : ℕ) (a : ℤ →₀ ℕ) :
    gaussianOffsetShiftedKey q a =
      Finsupp.mapDomain (fun z : ℤ => Int.toNat ((q : ℤ) + z)) a := by
  rfl

/-- Translating an atom key to signed offsets and back recovers the key exactly. -/
theorem gaussianOffsetShiftedKey_patternOfKey (q : ℕ) (ν : ℕ →₀ ℕ) :
    gaussianOffsetShiftedKey q (gaussianOffsetPatternOfKey q ν) = ν := by
  rw [gaussianOffsetShiftedKey_eq_mapDomain, gaussianOffsetPatternOfKey,
    ← Finsupp.mapDomain_comp]
  have hfun : ((fun z : ℤ => Int.toNat ((q : ℤ) + z)) ∘ centeredNatOffset q) = id := by
    funext i
    change Int.toNat ((q : ℤ) + ((i : ℤ) - (q : ℤ))) = i
    simp
  rw [hfun, Finsupp.mapDomain_id]

/-- Translating a bounded pattern through its original window or through its intrinsic signed
offset pattern gives exactly the same coefficient multiplicity key. -/
theorem shiftedAtomPatternKey_gaussianOffsetPatternOfWindow_eq
    {M D q K : ℕ} (p : Fin M → Fin (D + 1)) (hKq : K ≤ q) :
    shiftedAtomPatternKey q K p =
      gaussianOffsetShiftedKey q (gaussianOffsetPatternOfWindow K p) := by
  rw [shiftedAtomPatternKey, gaussianOffsetShiftedKey_eq_mapDomain,
    gaussianOffsetPatternOfWindow, ← Finsupp.mapDomain_comp]
  apply congrArg (fun f : ℕ → ℕ => Finsupp.mapDomain f (atomPatternKey p))
  funext r
  change windowShift q K r =
    Int.toNat ((q : ℤ) + ((r : ℤ) - (K : ℤ)))
  have hnonneg : 0 ≤ (q : ℤ) + ((r : ℤ) - (K : ℤ)) := by
    omega
  apply Int.ofNat_injective
  calc
    (windowShift q K r : ℤ) = (q : ℤ) + ((r : ℤ) - (K : ℤ)) := by
      dsimp [windowShift]
      omega
    _ = (Int.toNat ((q : ℤ) + ((r : ℤ) - (K : ℤ))) : ℤ) :=
      (Int.toNat_of_nonneg hnonneg).symm

theorem windowShift_eq_toNat_add_centeredIndex
    {R q : ℕ} (hRq : R ≤ q) (j : Fin (2 * R + 1)) :
    windowShift q R (j : ℕ) =
      Int.toNat ((q : ℤ) + (centeredIndexEquiv R j).1) := by
  change windowShift q R (j : ℕ) =
    Int.toNat ((q : ℤ) + (((j : ℕ) : ℤ) - (R : ℤ)))
  have hnonneg :
      0 ≤ (q : ℤ) + (((j : ℕ) : ℤ) - (R : ℤ)) := by
    omega
  apply Int.ofNat_injective
  calc
    (windowShift q R (j : ℕ) : ℤ) =
        (q : ℤ) + (((j : ℕ) : ℤ) - (R : ℤ)) := by
      dsimp [windowShift]
      omega
    _ = (Int.toNat ((q : ℤ) + (((j : ℕ) : ℤ) - (R : ℤ))) : ℤ) :=
      (Int.toNat_of_nonneg hnonneg).symm

/-- Every sufficiently translated centered-window key is exactly the canonical translated key
of the underlying global pattern.  This is the finite-window independence required to keep one
leading ADE atom fixed while the Gaussian face expands. -/
theorem shiftedAtomPatternKey_gaussianOffsetPatternWindow_eq
    {D : ℕ} {S : ℤ} {R q : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) (hRq : R ≤ q) :
    shiftedAtomPatternKey q R
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R) =
      gaussianOffsetShiftedKey q a := by
  classical
  have hsupp := (mem_gaussianOffsetFace.mp ha).2.1
  rw [shiftedAtomPatternKey_eq_sum]
  change (∑ j : Fin (2 * R + 1),
    Finsupp.single (windowShift q R (j : ℕ))
      (a ((centeredIndexEquiv R j).1))) = gaussianOffsetShiftedKey q a
  calc
    (∑ j : Fin (2 * R + 1),
        Finsupp.single (windowShift q R (j : ℕ))
          (a ((centeredIndexEquiv R j).1))) =
        ∑ j : Fin (2 * R + 1),
          Finsupp.single
            (Int.toNat ((q : ℤ) + (centeredIndexEquiv R j).1))
            (a ((centeredIndexEquiv R j).1)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [windowShift_eq_toNat_add_centeredIndex hRq j]
    _ = ∑ z : ↥(gaussianOffsetInterval R),
          Finsupp.single (Int.toNat ((q : ℤ) + z.1)) (a z.1) :=
      Equiv.sum_comp (centeredIndexEquiv R)
        (fun z => Finsupp.single (Int.toNat ((q : ℤ) + z.1)) (a z.1))
    _ = (gaussianOffsetInterval R).sum (fun z =>
          Finsupp.single (Int.toNat ((q : ℤ) + z)) (a z)) := by
      simpa using
        (Finset.sum_attach (gaussianOffsetInterval R) (fun z =>
          Finsupp.single (Int.toNat ((q : ℤ) + z)) (a z)))
    _ = gaussianOffsetShiftedKey q a := by
      rw [gaussianOffsetShiftedKey]
      symm
      apply Finset.sum_subset hsupp
      intro z _hzInterval hzSupport
      rw [Finsupp.notMem_support_iff.mp hzSupport]
      simp

/-- Exact Gaussian valuation of a translated intrinsic offset pattern. -/
theorem atomValuation_gaussianOffsetShiftedKey
    (B : ℝ) {D : ℕ} {S : ℤ} {R q : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) (hRq : R ≤ q) :
    atomValuation (fun i => B * (i : ℝ) ^ 2) (gaussianOffsetShiftedKey q a) =
      B * ((D : ℝ) * (q : ℝ) ^ 2 + 2 * (q : ℝ) * (S : ℝ) +
        (gaussianOffsetPatternEnergy a : ℝ)) := by
  let p := gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R
  have hpcount : (∑ j, (p j : ℕ)) = D := by
    simpa only [p] using gaussianOffsetPatternWindow_count ha
  have hsourceInt :
      (polynomialPatternSourceSum p : ℤ) - (R : ℤ) * (D : ℤ) = S := by
    simpa only [p] using gaussianOffsetPatternWindow_source ha
  have hsourceR :
      (polynomialPatternSourceSum p : ℝ) =
        (S : ℝ) + (R : ℝ) * (D : ℝ) := by
    exact_mod_cast (by linarith [hsourceInt] :
      (polynomialPatternSourceSum p : ℤ) = S + (R : ℤ) * (D : ℤ))
  have henergyInt :
      (∑ j : Fin (2 * R + 1),
        (((j : ℕ) : ℤ) - (R : ℤ)) ^ 2 * ((p j : ℕ) : ℤ)) =
        gaussianOffsetPatternEnergy a := by
    simpa only [p] using gaussianOffsetPatternWindow_energy ha
  have hmoment2Int :
      (polynomialPatternMoment p 2 : ℤ) =
        ∑ j : Fin (2 * R + 1),
          ((j : ℤ) ^ 2 * ((p j : ℕ) : ℤ)) := by
    rw [polynomialPatternMoment]
    push_cast
    simpa only [mul_comm]
  have hmoment1Int :
      (polynomialPatternSourceSum p : ℤ) =
        ∑ j : Fin (2 * R + 1),
          ((j : ℤ) * ((p j : ℕ) : ℤ)) := by
    rw [polynomialPatternSourceSum]
    push_cast
    rfl
  have hcountInt :
      (D : ℤ) = ∑ j : Fin (2 * R + 1), ((p j : ℕ) : ℤ) := by
    exact_mod_cast hpcount.symm
  have henergyExpandInt :
      gaussianOffsetPatternEnergy a =
        (polynomialPatternMoment p 2 : ℤ) -
          2 * (R : ℤ) * (polynomialPatternSourceSum p : ℤ) +
            (R : ℤ) ^ 2 * (D : ℤ) := by
    rw [← henergyInt, hmoment2Int, hmoment1Int, hcountInt,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have henergyExpandR :
      (gaussianOffsetPatternEnergy a : ℝ) =
        (polynomialPatternMoment p 2 : ℝ) -
          2 * (R : ℝ) * (polynomialPatternSourceSum p : ℝ) +
            (R : ℝ) ^ 2 * (D : ℝ) := by
    exact_mod_cast henergyExpandInt
  rw [← shiftedAtomPatternKey_gaussianOffsetPatternWindow_eq ha hRq]
  change atomValuation (fun i => B * (i : ℝ) ^ 2) (shiftedAtomPatternKey q R p) = _
  have hshift := atomValuation_shiftedAtomPatternKey
    (β := (2 : ℝ)) (B := B) p hRq
  simp only [Real.rpow_two] at hshift
  rw [hshift,
    polynomialPatternPowerValuation_two p ((q : ℝ) - R) hpcount]
  rw [polynomialPatternMoment_one]
  change B * ((D : ℝ) * ((q : ℝ) - R) ^ 2 +
      2 * ((q : ℝ) - R) * (polynomialPatternSourceSum p : ℝ) +
        (polynomialPatternMoment p 2 : ℝ)) = _
  rw [hsourceR]
  nlinarith [henergyExpandR]

/-- Enlarging the centered display window leaves the translated multiplicity key unchanged. -/
theorem shiftedAtomPatternKey_gaussianOffsetPatternWindow_eq_of_le
    {D : ℕ} {S : ℤ} {R R' q : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) (hRR' : R ≤ R') (hR'q : R' ≤ q) :
    shiftedAtomPatternKey q R
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R) =
      shiftedAtomPatternKey q R'
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount (gaussianOffsetFace_mono hRR' ha)) R') := by
  calc
    shiftedAtomPatternKey q R
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R) =
        gaussianOffsetShiftedKey q a :=
      shiftedAtomPatternKey_gaussianOffsetPatternWindow_eq ha (hRR'.trans hR'q)
    _ = shiftedAtomPatternKey q R'
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount (gaussianOffsetFace_mono hRR' ha)) R') :=
      (shiftedAtomPatternKey_gaussianOffsetPatternWindow_eq
        (gaussianOffsetFace_mono hRR' ha) hR'q).symm

/-! ## Uniform grouped-weight bounds -/

/-- The translation polynomial of one labelled assignment has degree at most the total jet order
of its differential monomial. -/
theorem natDegree_polynomialPatternAssignmentPoly_le
    {n D K τ M : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p)) (g : Fin D → Fin M) :
    (polynomialPatternAssignmentPoly m g).natDegree ≤
      jetMonomialOrder n m.1 := by
  rw [polynomialPatternAssignmentPoly]
  calc
    (∏ t : Fin (jetMonomialDegree n m.1),
        (descPochhammer ℂ (flatOrder (fun j => m.1 j.succ) t)).comp
          (Polynomial.X + Polynomial.C
            (((((g (polynomialPatternJetCast m t) : Fin M) : ℕ) : ℤ) -
              (K : ℤ) : ℤ) : ℂ))).natDegree
        ≤ ∑ t : Fin (jetMonomialDegree n m.1),
            ((descPochhammer ℂ (flatOrder (fun j => m.1 j.succ) t)).comp
              (Polynomial.X + Polynomial.C
                (((((g (polynomialPatternJetCast m t) : Fin M) : ℕ) : ℤ) -
                  (K : ℤ) : ℤ) : ℂ))).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ t : Fin (jetMonomialDegree n m.1),
          flatOrder (fun j => m.1 j.succ) t := by
      apply Finset.sum_le_sum
      intro t _ht
      calc
        ((descPochhammer ℂ (flatOrder (fun j => m.1 j.succ) t)).comp
            (Polynomial.X + Polynomial.C
              (((((g (polynomialPatternJetCast m t) : Fin M) : ℕ) : ℤ) -
                (K : ℤ) : ℤ) : ℂ))).natDegree
            ≤ (descPochhammer ℂ (flatOrder (fun j => m.1 j.succ) t)).natDegree *
              (Polynomial.X + Polynomial.C
                (((((g (polynomialPatternJetCast m t) : Fin M) : ℕ) : ℤ) -
                  (K : ℤ) : ℤ) : ℂ)).natDegree := Polynomial.natDegree_comp_le
        _ = flatOrder (fun j => m.1 j.succ) t := by
          rw [descPochhammer_natDegree, Polynomial.natDegree_X_add_C, mul_one]
    _ = jetMonomialOrder n m.1 := by
      simpa [jetMonomialOrder] using
        (flatOrder_sum (fun j => m.1 j.succ))

/-- A common order bound for the active jet group is also a degree bound for its grouped pattern
weight polynomial. -/
theorem natDegree_polynomialPatternWeightPoly_le_of_order_le
    {n D K τ M H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1))
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    (polynomialPatternWeightPoly n D K τ Q p).natDegree ≤ H := by
  classical
  rw [polynomialPatternWeightPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _hm
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hinner :
      (∑ g ∈ atomPatternAssignments p,
        polynomialPatternAssignmentPoly m g).natDegree ≤ H := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro g _hg
    exact (natDegree_polynomialPatternAssignmentPoly_le m g).trans (horder m)
  simpa using hinner

/-- In particular, the maximal jet order bounds the degree of every grouped pattern weight. -/
theorem natDegree_polynomialPatternWeightPoly_le_maxJetOrder
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) :
    (polynomialPatternWeightPoly n D K τ Q p).natDegree ≤
      magnitudeMaxJetOrder n Q := by
  apply natDegree_polynomialPatternWeightPoly_le_of_order_le Q p
  intro m
  exact jetOrder_le_magnitudeMaxJetOrder Q
    (Finset.mem_filter.mp m.2).1

/-- The corresponding integer grouped weight has the same uniform degree bound. -/
theorem natDegree_polynomialPatternWeightPolyInt_le_maxJetOrder
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (c : (Fin (n + 2) →₀ ℕ) → ℤ)
    (hc : ∀ m, MvPolynomial.coeff m Q = (c m : ℂ))
    (p : Fin M → Fin (D + 1)) :
    (polynomialPatternWeightPolyInt n D K τ Q c p).natDegree ≤
      magnitudeMaxJetOrder n Q := by
  have hdeg := natDegree_polynomialPatternWeightPoly_le_maxJetOrder
    (K := K) (τ := τ) Q p
  rw [← map_polynomialPatternWeightPolyInt n D K τ Q c hc p,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective] at hdeg
  exact hdeg

/-- Two complex polynomials which agree at all sufficiently large natural arguments are equal. -/
theorem complexPolynomial_eq_of_eventually_eval_nat_eq
    (P Q : Polynomial ℂ)
    (h : ∀ᶠ q : ℕ in atTop, P.eval (q : ℂ) = Q.eval (q : ℂ)) :
    P = Q := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  let orbit : ℕ → ℂ := fun k => ((N + k : ℕ) : ℂ)
  have horbit : Function.Injective orbit := by
    intro i j hij
    change ((N + i : ℕ) : ℂ) = ((N + j : ℕ) : ℂ) at hij
    have hijNat : N + i = N + j := by
      exact_mod_cast hij
    omega
  apply Polynomial.eq_of_infinite_eval_eq P Q
  apply (Set.infinite_range_of_injective horbit).mono
  rintro z ⟨k, rfl⟩
  simpa only [orbit] using hN (N + k) (by omega)

/-- The grouped ADE weight of one global offset pattern has the same value in every larger
centered display window, once the translation is large enough for both polynomial presentations.
The equality is exact, because both sides evaluate `aevalWeight` on the same canonical key. -/
theorem eval_polynomialPatternWeightPoly_gaussianOffsetPatternWindow_eq_of_le
    {n D τ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {S : ℤ} {R R' q : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) (hRR' : R ≤ R')
    (hlarge : R' + n ≤ q) :
    (polynomialPatternWeightPoly n D R τ Q
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R)).eval
          (q : ℂ) =
      (polynomialPatternWeightPoly n D R' τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount (gaussianOffsetFace_mono hRR' ha)) R')).eval
            (q : ℂ) := by
  calc
    (polynomialPatternWeightPoly n D R τ Q
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R)).eval
          (q : ℂ) =
        aevalWeight n (D * q + τ) Q
          (shiftedAtomPatternKey q R
            (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R)) :=
      (aevalWeight_shiftedAtomPatternKey_eq_eval_poly n D R τ Q
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R)
        (gaussianOffsetPatternWindow_count ha) (by omega)).symm
    _ = aevalWeight n (D * q + τ) Q
          (shiftedAtomPatternKey q R'
            (gaussianOffsetPatternWindow a
              (gaussianOffsetFace_totalCount (gaussianOffsetFace_mono hRR' ha)) R')) := by
      rw [shiftedAtomPatternKey_gaussianOffsetPatternWindow_eq_of_le
        ha hRR' (by omega)]
    _ = (polynomialPatternWeightPoly n D R' τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount (gaussianOffsetFace_mono hRR' ha)) R')).eval
            (q : ℂ) :=
      aevalWeight_shiftedAtomPatternKey_eq_eval_poly n D R' τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount (gaussianOffsetFace_mono hRR' ha)) R')
        (gaussianOffsetPatternWindow_count (gaussianOffsetFace_mono hRR' ha)) hlarge

/-- The complete grouped weight polynomial of a global offset pattern is independent of the
centered window used to display it.  Eventual exact evaluation equality upgrades to polynomial
equality, so every coefficient—not merely a preselected maximal-order coefficient—is stable. -/
theorem polynomialPatternWeightPoly_gaussianOffsetPatternWindow_eq_of_le
    {n D τ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {S : ℤ} {R R' : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) (hRR' : R ≤ R') :
    polynomialPatternWeightPoly n D R τ Q
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R) =
      polynomialPatternWeightPoly n D R' τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount (gaussianOffsetFace_mono hRR' ha)) R') := by
  apply complexPolynomial_eq_of_eventually_eval_nat_eq
  filter_upwards [eventually_ge_atTop (R' + n)] with q hq
  exact eval_polynomialPatternWeightPoly_gaussianOffsetPatternWindow_eq_of_le
    Q ha hRR' hq

/-- Any common active-order bound supplies coefficientwise convergence after normalization by
that order. -/
theorem tendsto_polynomialPatternWeightPoly_eval_div_pow_of_order_le
    {n D K τ M H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1))
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    Tendsto (fun q : ℕ =>
      (polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) /
        (q : ℂ) ^ H) atTop
      (𝓝 ((polynomialPatternWeightPoly n D K τ Q p).coeff H)) := by
  exact tendsto_complexPolynomial_eval_nat_div_pow _
    (natDegree_polynomialPatternWeightPoly_le_of_order_le Q p horder)

/-- The integer-polynomial presentation has the same normalized complex limit. -/
theorem tendsto_polynomialPatternWeightPolyInt_eval_div_pow_of_order_le
    {n D K τ M H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (c : (Fin (n + 2) →₀ ℕ) → ℤ)
    (hc : ∀ m, MvPolynomial.coeff m Q = (c m : ℂ))
    (p : Fin M → Fin (D + 1))
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    Tendsto (fun q : ℕ =>
      (((polynomialPatternWeightPolyInt n D K τ Q c p).eval (q : ℤ) : ℤ) : ℂ) /
        (q : ℂ) ^ H) atTop
      (𝓝 ((polynomialPatternWeightPoly n D K τ Q p).coeff H)) := by
  apply (tendsto_polynomialPatternWeightPoly_eval_div_pow_of_order_le
    Q p horder).congr'
  apply Eventually.of_forall
  intro q
  apply congrArg (fun z : ℂ => z / (q : ℂ) ^ H)
  rw [← map_polynomialPatternWeightPolyInt n D K τ Q c hc p]
  exact (Polynomial.eval_map_apply (p :=
    polynomialPatternWeightPolyInt n D K τ Q c p)
      (Int.castRingHom ℂ) (q : ℤ))

/-- Coefficientwise maximal-order normalization of every grouped pattern weight converges to its
maximal-order coefficient. -/
theorem tendsto_polynomialPatternWeightPoly_eval_div_pow_maxJetOrder
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) :
    Tendsto (fun q : ℕ =>
      (polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) /
        (q : ℂ) ^ magnitudeMaxJetOrder n Q) atTop
      (𝓝 ((polynomialPatternWeightPoly n D K τ Q p).coeff
        (magnitudeMaxJetOrder n Q))) := by
  apply tendsto_polynomialPatternWeightPoly_eval_div_pow_of_order_le Q p
  intro m
  exact jetOrder_le_magnitudeMaxJetOrder Q
    (Finset.mem_filter.mp m.2).1

/-- Every coefficient is independent of the centered window used to display a fixed global
offset pattern. -/
theorem coeff_polynomialPatternWeightPoly_gaussianOffsetPatternWindow_eq_of_le
    {n D τ H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {S : ℤ} {R R' : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) (hRR' : R ≤ R') :
    (polynomialPatternWeightPoly n D R τ Q
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R)).coeff H =
      (polynomialPatternWeightPoly n D R' τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount (gaussianOffsetFace_mono hRR' ha)) R')).coeff H := by
  exact congrArg (fun P : Polynomial ℂ => P.coeff H)
    (polynomialPatternWeightPoly_gaussianOffsetPatternWindow_eq_of_le Q ha hRR')

/-- In particular, the maximal-order coefficient of a fixed global offset atom is stable under
every enlargement of its centered window. -/
theorem coeff_maxJetOrder_polynomialPatternWeightPoly_gaussianOffsetPatternWindow_eq_of_le
    {n D τ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {S : ℤ} {R R' : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) (hRR' : R ≤ R') :
    (polynomialPatternWeightPoly n D R τ Q
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R)).coeff
          (magnitudeMaxJetOrder n Q) =
      (polynomialPatternWeightPoly n D R' τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount (gaussianOffsetFace_mono hRR' ha)) R')).coeff
            (magnitudeMaxJetOrder n Q) := by
  exact coeff_polynomialPatternWeightPoly_gaussianOffsetPatternWindow_eq_of_le
    Q ha hRR'

/-- Strengthened bounded balanced survivor retaining the exact anchor grading invariant.  This
is the datum which identifies the resulting intrinsic signed-offset pattern with the least
top-degree source face, rather than merely with some nonzero face. -/
theorem exists_eventually_boundedPattern_nonzero_aevalWeight_residue_with_invariant
    {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ}
    (ha : anchor ∈ Q.support) (hD : 0 < jetMonomialDegree n anchor)
    (τ : ℕ) (hτ : τ < jetMonomialDegree n anchor) :
    ∃ (K M : ℕ)
        (p : Fin M → Fin (jetMonomialDegree n anchor + 1)) (Q₀ : ℕ),
      (∑ r, (p r : ℕ)) = jetMonomialDegree n anchor ∧
        ∀ q ≥ Q₀,
          shiftedAtomPatternKey q K p ∈
              (sigmaIdx n (jetMonomialDegree n anchor * q + τ) Q).image (atomKeyOf n) ∧
            aevalWeight n (jetMonomialDegree n anchor * q + τ) Q
                (shiftedAtomPatternKey q K p) ≠ 0 ∧
            (shiftedAtomPatternKey q K p).sum (fun i k => i * k) +
                magnitudeShiftCode n Q anchor =
              jetMonomialDegree n anchor * q + τ + magnitudeMaxJetOrder n Q := by
  classical
  let D := jetMonomialDegree n anchor
  obtain ⟨K, δ, Q₀, hres⟩ :=
    exists_eventually_balancedKey_nonzero_exact_residue ha hD τ hτ
  let M := magnitudeOffsetMax δ + 1
  have hδM : ∀ i, δ i < M := by
    intro i
    exact (offset_le_magnitudeOffsetMax δ i).trans_lt (by dsimp [M]; omega)
  have hkeyCount : (key δ).sum (fun _ k => k) = D := key_total_count δ
  have hkeySupport : ∀ r, key δ r ≠ 0 → r < M := by
    intro r hr
    rw [key_count_map] at hr
    have hrmem : r ∈ Multiset.map δ (Finset.univ : Finset (Fin D)).val :=
      Multiset.count_ne_zero.mp hr
    rw [Multiset.mem_map] at hrmem
    obtain ⟨i, _hi, hir⟩ := hrmem
    simpa [← hir] using hδM i
  let p : Fin M → Fin (D + 1) :=
    boundedPatternOfFinsupp (key δ) D M hkeyCount
  have hpcount : (∑ r, (p r : ℕ)) = D :=
    boundedPatternOfFinsupp_count (key δ) D M hkeyCount hkeySupport
  let g : Fin D → Fin M := fun i => ⟨δ i, hδM i⟩
  have hg : g ∈ atomPatternAssignments p := by
    rw [mem_atomPatternAssignments]
    change key δ = atomPatternKey p
    exact (atomPatternKey_boundedPatternOfFinsupp
      (key δ) D M hkeyCount hkeySupport).symm
  refine ⟨K, M, p, Q₀, by simpa only [D] using hpcount, ?_⟩
  intro q hq
  have hdata := hres q hq
  dsimp only at hdata
  let s : Fin D → ℕ := fun i => q - K + δ i
  have hkeyEq : shiftedAtomPatternKey q K p = key s := by
    calc
      shiftedAtomPatternKey q K p =
          key (fun i => windowShift q K (g i : ℕ)) :=
        (key_windowShift_eq_shiftedAtomPatternKey p g hg).symm
      _ = key s := by
        apply congrArg key
        funext i
        rfl
  have hmem : key s ∈
      (sigmaIdx n (D * q + τ) Q).image (atomKeyOf n) := by
    simpa only [D, s] using hdata.1
  have hweight : aevalWeight n (D * q + τ) Q (key s) ≠ 0 := by
    simpa only [D, s] using hdata.2.1
  have hinvariant :
      (key s).sum (fun i k => i * k) + magnitudeShiftCode n Q anchor =
        D * q + τ + magnitudeMaxJetOrder n Q := by
    simpa only [D, s] using hdata.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hkeyEq]
    simpa only [D] using hmem
  · rw [hkeyEq]
    simpa only [D] using hweight
  · rw [hkeyEq]
    simpa only [D] using hinvariant

/-- Balanced survival produces one intrinsic Gaussian-face atom whose grouped weight has a fixed
nonzero leading coefficient.  Its degree is bounded by the ADE's maximal jet order, and the
preceding window-independence theorem keeps this exact coefficient unchanged on every larger
Gaussian face. -/
theorem exists_gaussianOffsetFace_fixed_nonzero_leadingCoefficient
    {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ}
    (ha : anchor ∈ Q.support) (hD : 0 < jetMonomialDegree n anchor)
    (τ : ℕ) (hτ : τ < jetMonomialDegree n anchor) :
    ∃ (S : ℤ) (R H : ℕ) (a : ℤ →₀ ℕ)
        (haFace : a ∈ gaussianOffsetFace (jetMonomialDegree n anchor) S R),
      S + (magnitudeShiftCode n Q anchor : ℤ) =
          ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ) ∧
        H ≤ magnitudeMaxJetOrder n Q ∧
        (polynomialPatternWeightPoly n (jetMonomialDegree n anchor) R τ Q
          (gaussianOffsetPatternWindow a
            (gaussianOffsetFace_totalCount haFace) R)).coeff H ≠ 0 := by
  classical
  let D := jetMonomialDegree n anchor
  change ∃ (S : ℤ) (R H : ℕ) (a : ℤ →₀ ℕ)
      (haFace : a ∈ gaussianOffsetFace D S R),
    S + (magnitudeShiftCode n Q anchor : ℤ) =
        ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ) ∧
      H ≤ magnitudeMaxJetOrder n Q ∧
      (polynomialPatternWeightPoly n D R τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount haFace) R)).coeff H ≠ 0
  obtain ⟨K, M, p, Q₀, hpcount, hp⟩ :=
    exists_eventually_boundedPattern_nonzero_aevalWeight_residue_with_invariant
      ha hD τ hτ
  let a : ℤ →₀ ℕ := gaussianOffsetPatternOfWindow K p
  let R : ℕ := K + M
  let S : ℤ := gaussianOffsetSource a
  have haFace : a ∈ gaussianOffsetFace D S R := by
    dsimp only [a, S, R]
    exact gaussianOffsetPatternOfWindow_mem_face p (by simpa [D] using hpcount)
  let pR := gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount haFace) R
  let W := polynomialPatternWeightPoly n D R τ Q pR
  let q := max Q₀ (max (K + n) (R + n))
  have hq₀ : Q₀ ≤ q := by
    dsimp [q]
    omega
  have hKq : K ≤ q := by
    dsimp [q]
    omega
  have hRq : R ≤ q := by
    dsimp [q]
    omega
  have hRlarge : R + n ≤ q := by
    dsimp [q]
    omega
  have hsurvivor := hp q hq₀
  have hsourceFloorNat :
      polynomialPatternSourceSum p + magnitudeShiftCode n Q anchor =
        D * K + τ + magnitudeMaxJetOrder n Q := by
    exact polynomialPattern_source_floor_eq_of_anchor_invariant
      p (by simpa only [D] using hpcount) hKq (by
        simpa only [D] using hsurvivor.2.2)
  have hsourceFloorInt :
      (polynomialPatternSourceSum p : ℤ) +
          (magnitudeShiftCode n Q anchor : ℤ) =
        (D : ℤ) * (K : ℤ) + (τ : ℤ) +
          (magnitudeMaxJetOrder n Q : ℤ) := by
    exact_mod_cast hsourceFloorNat
  have hglobalSource :
      S + (magnitudeShiftCode n Q anchor : ℤ) =
        ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ) := by
    dsimp only [S, a]
    rw [gaussianOffsetSource_patternOfWindow p (by simpa only [D] using hpcount)]
    calc
      (polynomialPatternSourceSum p : ℤ) - (K : ℤ) * (D : ℤ) +
          (magnitudeShiftCode n Q anchor : ℤ) =
          ((polynomialPatternSourceSum p : ℤ) +
            (magnitudeShiftCode n Q anchor : ℤ)) -
              (K : ℤ) * (D : ℤ) := by ring
      _ = ((D : ℤ) * (K : ℤ) + (τ : ℤ) +
            (magnitudeMaxJetOrder n Q : ℤ)) -
              (K : ℤ) * (D : ℤ) := by rw [hsourceFloorInt]
      _ = ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ) := by
        push_cast
        ring
  have hkeyOriginal :
      shiftedAtomPatternKey q K p = gaussianOffsetShiftedKey q a := by
    simpa only [a] using
      shiftedAtomPatternKey_gaussianOffsetPatternOfWindow_eq p hKq
  have hkeyCentered :
      shiftedAtomPatternKey q R pR = gaussianOffsetShiftedKey q a := by
    simpa only [pR] using
      shiftedAtomPatternKey_gaussianOffsetPatternWindow_eq haFace hRq
  have hweight :
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q R pR) ≠ 0 := by
    rw [hkeyCentered, ← hkeyOriginal]
    simpa only [D] using hsurvivor.2.1
  have heval : W.eval (q : ℂ) ≠ 0 := by
    change (polynomialPatternWeightPoly n D R τ Q pR).eval (q : ℂ) ≠ 0
    rw [← aevalWeight_shiftedAtomPatternKey_eq_eval_poly n D R τ Q pR
      (gaussianOffsetPatternWindow_count haFace) hRlarge]
    exact hweight
  have hW : W ≠ 0 := by
    intro hzero
    apply heval
    rw [hzero, Polynomial.eval_zero]
  have hdegree : W.natDegree ≤ magnitudeMaxJetOrder n Q := by
    change (polynomialPatternWeightPoly n D R τ Q pR).natDegree ≤
      magnitudeMaxJetOrder n Q
    exact natDegree_polynomialPatternWeightPoly_le_maxJetOrder Q pR
  have hlead : W.coeff W.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hW
  refine ⟨S, R, W.natDegree, a, haFace, hglobalSource, hdegree, ?_⟩
  change W.coeff W.natDegree ≠ 0
  exact hlead

/-- Packaged fixed-atom form: one nonzero leading coefficient survives identically through every
larger centered Gaussian face. -/
theorem exists_gaussianOffsetFace_stable_nonzero_leadingCoefficient
    {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ}
    (ha : anchor ∈ Q.support) (hD : 0 < jetMonomialDegree n anchor)
    (τ : ℕ) (hτ : τ < jetMonomialDegree n anchor) :
    ∃ (S : ℤ) (R H : ℕ) (a : ℤ →₀ ℕ)
        (haFace : a ∈ gaussianOffsetFace (jetMonomialDegree n anchor) S R)
        (ell : ℂ),
      S + (magnitudeShiftCode n Q anchor : ℤ) =
          ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ) ∧
        H ≤ magnitudeMaxJetOrder n Q ∧ ell ≠ 0 ∧
          ∀ (R' : ℕ) (hRR' : R ≤ R'),
            (polynomialPatternWeightPoly n (jetMonomialDegree n anchor) R' τ Q
              (gaussianOffsetPatternWindow a
                (gaussianOffsetFace_totalCount
                  (gaussianOffsetFace_mono hRR' haFace)) R')).coeff H = ell := by
  obtain ⟨S, R, H, a, haFace, hsource, hH, hcoeff⟩ :=
    exists_gaussianOffsetFace_fixed_nonzero_leadingCoefficient ha hD τ hτ
  let ell :=
    (polynomialPatternWeightPoly n (jetMonomialDegree n anchor) R τ Q
      (gaussianOffsetPatternWindow a
        (gaussianOffsetFace_totalCount haFace) R)).coeff H
  refine ⟨S, R, H, a, haFace, ell, hsource, hH, ?_, ?_⟩
  · simpa only [ell] using hcoeff
  · intro R' hRR'
    simpa only [ell] using
      (coeff_polynomialPatternWeightPoly_gaussianOffsetPatternWindow_eq_of_le
        (H := H) Q haFace hRR').symm

/-- Every nonzero top-degree grouped weight lies on or above the anchor source floor.  This is the
global signed-offset form of `polynomialPattern_source_floor_of_survivor`. -/
theorem gaussianOffsetSource_floor_of_weightPoly_ne_zero
    {n D τ : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ}
    (haD : jetMonomialDegree n anchor = D)
    (haMax : ∀ m ∈ Q.support,
      jetMonomialDegree n m = D →
        magnitudeShiftCode n Q m ≤ magnitudeShiftCode n Q anchor)
    {T : ℤ} {R : ℕ} {a : ℤ →₀ ℕ}
    (haFace : a ∈ gaussianOffsetFace D T R)
    (hpoly : polynomialPatternWeightPoly n D R τ Q
      (gaussianOffsetPatternWindow a
        (gaussianOffsetFace_totalCount haFace) R) ≠ 0) :
    (((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ) -
        (magnitudeShiftCode n Q anchor : ℤ)) ≤ T := by
  let p := gaussianOffsetPatternWindow a
    (gaussianOffsetFace_totalCount haFace) R
  have hpcount : (∑ r, (p r : ℕ)) = D := by
    simpa only [p] using gaussianOffsetPatternWindow_count haFace
  have hpSurvivor : p ∈ polynomialPatternSurvivors n D R τ Q (2 * R + 1) := by
    rw [polynomialPatternSurvivors, degreeDPolynomialPatterns,
      Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ p, hpcount⟩, by simpa only [p] using hpoly⟩
  have hfloor := polynomialPattern_source_floor_of_survivor
    haD haMax hpSurvivor
  have hfloorInt :
      (D : ℤ) * (R : ℤ) + (τ : ℤ) +
          (magnitudeMaxJetOrder n Q : ℤ) ≤
        (polynomialPatternSourceSum p : ℤ) +
          (magnitudeShiftCode n Q anchor : ℤ) := by
    exact_mod_cast hfloor
  have hsource :
      (polynomialPatternSourceSum p : ℤ) - (R : ℤ) * (D : ℤ) = T := by
    simpa only [p] using gaussianOffsetPatternWindow_source haFace
  push_cast
  rw [← hsource]
  nlinarith [hfloorInt]

/-- Consequently, the source returned by the stable balanced atom is the least signed source of
every nonzero top-degree global pattern. -/
theorem gaussianOffsetSource_le_of_anchor_floor_eq
    {n D τ : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ}
    (haD : jetMonomialDegree n anchor = D)
    (haMax : ∀ m ∈ Q.support,
      jetMonomialDegree n m = D →
        magnitudeShiftCode n Q m ≤ magnitudeShiftCode n Q anchor)
    {S T : ℤ}
    (hS : S + (magnitudeShiftCode n Q anchor : ℤ) =
      ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ))
    {R : ℕ} {a : ℤ →₀ ℕ}
    (haFace : a ∈ gaussianOffsetFace D T R)
    (hpoly : polynomialPatternWeightPoly n D R τ Q
      (gaussianOffsetPatternWindow a
        (gaussianOffsetFace_totalCount haFace) R) ≠ 0) :
    S ≤ T := by
  have hfloor := gaussianOffsetSource_floor_of_weightPoly_ne_zero
    haD haMax haFace hpoly
  nlinarith

/-- The finite set of polynomial degrees actually attained by nonzero global patterns on one
signed-source face.  Finiteness comes from the universal maximal jet-order bound, not from
finiteness of the Gaussian face itself. -/
noncomputable def gaussianOffsetActiveWeightDegrees
    (n D τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (S : ℤ) : Finset ℕ := by
  classical
  exact (Finset.range (magnitudeMaxJetOrder n Q + 1)).filter fun H =>
    ∃ (R : ℕ) (a : ℤ →₀ ℕ)
      (haFace : a ∈ gaussianOffsetFace D S R),
        polynomialPatternWeightPoly n D R τ Q
            (gaussianOffsetPatternWindow a
              (gaussianOffsetFace_totalCount haFace) R) ≠ 0 ∧
          (polynomialPatternWeightPoly n D R τ Q
            (gaussianOffsetPatternWindow a
              (gaussianOffsetFace_totalCount haFace) R)).natDegree = H

/-- The least Gaussian face has one maximal-degree atom with a fixed nonzero leading coefficient,
and that degree simultaneously bounds every other grouped weight on the complete infinite face. -/
theorem exists_gaussianOffsetFace_maximal_stable_nonzero_leadingCoefficient
    {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ}
    (ha : anchor ∈ Q.support) (hD : 0 < jetMonomialDegree n anchor)
    (τ : ℕ) (hτ : τ < jetMonomialDegree n anchor) :
    ∃ (S : ℤ) (H R : ℕ) (a : ℤ →₀ ℕ)
        (haFace : a ∈ gaussianOffsetFace (jetMonomialDegree n anchor) S R)
        (ell : ℂ),
      S + (magnitudeShiftCode n Q anchor : ℤ) =
          ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ) ∧
        H ≤ magnitudeMaxJetOrder n Q ∧ ell ≠ 0 ∧
        (∀ (R' : ℕ) (hRR' : R ≤ R'),
          (polynomialPatternWeightPoly n (jetMonomialDegree n anchor) R' τ Q
            (gaussianOffsetPatternWindow a
              (gaussianOffsetFace_totalCount
                (gaussianOffsetFace_mono hRR' haFace)) R')).coeff H = ell) ∧
        ∀ (R' : ℕ) (b : ℤ →₀ ℕ)
            (hbFace : b ∈
              gaussianOffsetFace (jetMonomialDegree n anchor) S R'),
          (polynomialPatternWeightPoly n (jetMonomialDegree n anchor) R' τ Q
            (gaussianOffsetPatternWindow b
              (gaussianOffsetFace_totalCount hbFace) R')).natDegree ≤ H := by
  classical
  let D := jetMonomialDegree n anchor
  change ∃ (S : ℤ) (H R : ℕ) (a : ℤ →₀ ℕ)
      (haFace : a ∈ gaussianOffsetFace D S R) (ell : ℂ),
    S + (magnitudeShiftCode n Q anchor : ℤ) =
        ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ) ∧
      H ≤ magnitudeMaxJetOrder n Q ∧ ell ≠ 0 ∧
      (∀ (R' : ℕ) (hRR' : R ≤ R'),
        (polynomialPatternWeightPoly n D R' τ Q
          (gaussianOffsetPatternWindow a
            (gaussianOffsetFace_totalCount
              (gaussianOffsetFace_mono hRR' haFace)) R')).coeff H = ell) ∧
      ∀ (R' : ℕ) (b : ℤ →₀ ℕ)
          (hbFace : b ∈ gaussianOffsetFace D S R'),
        (polynomialPatternWeightPoly n D R' τ Q
          (gaussianOffsetPatternWindow b
            (gaussianOffsetFace_totalCount hbFace) R')).natDegree ≤ H
  obtain ⟨S, R₀, H₀, a₀, ha₀, hsource, _hH₀, hcoeff₀⟩ :=
    exists_gaussianOffsetFace_fixed_nonzero_leadingCoefficient ha hD τ hτ
  let P₀ := polynomialPatternWeightPoly n D R₀ τ Q
    (gaussianOffsetPatternWindow a₀ (gaussianOffsetFace_totalCount ha₀) R₀)
  have hP₀ : P₀ ≠ 0 := by
    intro hzero
    apply hcoeff₀
    change P₀.coeff H₀ = 0
    rw [hzero, Polynomial.coeff_zero]
  have hP₀degree : P₀.natDegree ≤ magnitudeMaxJetOrder n Q := by
    change (polynomialPatternWeightPoly n D R₀ τ Q
      (gaussianOffsetPatternWindow a₀
        (gaussianOffsetFace_totalCount ha₀) R₀)).natDegree ≤
        magnitudeMaxJetOrder n Q
    exact natDegree_polynomialPatternWeightPoly_le_maxJetOrder Q _
  let degrees := gaussianOffsetActiveWeightDegrees n D τ Q S
  have hP₀mem : P₀.natDegree ∈ degrees := by
    change P₀.natDegree ∈ gaussianOffsetActiveWeightDegrees n D τ Q S
    rw [gaussianOffsetActiveWeightDegrees, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hP₀degree),
      R₀, a₀, ha₀, ?_, rfl⟩
    simpa only [P₀] using hP₀
  have hdegrees : degrees.Nonempty := ⟨P₀.natDegree, hP₀mem⟩
  let H := degrees.max' hdegrees
  have hHmem : H ∈ degrees := Finset.max'_mem degrees hdegrees
  have hHdata := hHmem
  change H ∈ gaussianOffsetActiveWeightDegrees n D τ Q S at hHdata
  rw [gaussianOffsetActiveWeightDegrees, Finset.mem_filter] at hHdata
  obtain ⟨hHrange, R, a, haFace, hP, hdegree⟩ := hHdata
  let P := polynomialPatternWeightPoly n D R τ Q
    (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount haFace) R)
  let ell := P.coeff H
  have hHle : H ≤ magnitudeMaxJetOrder n Q := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hHrange)
  have hell : ell ≠ 0 := by
    dsimp only [ell]
    rw [← hdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (by simpa only [P] using hP)
  have hstable : ∀ (R' : ℕ) (hRR' : R ≤ R'),
      (polynomialPatternWeightPoly n D R' τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount
            (gaussianOffsetFace_mono hRR' haFace)) R')).coeff H = ell := by
    intro R' hRR'
    simpa only [ell, P] using
      (coeff_polynomialPatternWeightPoly_gaussianOffsetPatternWindow_eq_of_le
        (H := H) Q haFace hRR').symm
  have huniform : ∀ (R' : ℕ) (b : ℤ →₀ ℕ)
      (hbFace : b ∈ gaussianOffsetFace D S R'),
      (polynomialPatternWeightPoly n D R' τ Q
        (gaussianOffsetPatternWindow b
          (gaussianOffsetFace_totalCount hbFace) R')).natDegree ≤ H := by
    intro R' b hbFace
    let Pb := polynomialPatternWeightPoly n D R' τ Q
      (gaussianOffsetPatternWindow b
        (gaussianOffsetFace_totalCount hbFace) R')
    by_cases hPb : Pb = 0
    · simp only [Pb, hPb, Polynomial.natDegree_zero, Nat.zero_le]
    · have hPbDegree : Pb.natDegree ≤ magnitudeMaxJetOrder n Q := by
        change (polynomialPatternWeightPoly n D R' τ Q
          (gaussianOffsetPatternWindow b
            (gaussianOffsetFace_totalCount hbFace) R')).natDegree ≤
              magnitudeMaxJetOrder n Q
        exact natDegree_polynomialPatternWeightPoly_le_maxJetOrder Q _
      have hPbmem : Pb.natDegree ∈ degrees := by
        change Pb.natDegree ∈ gaussianOffsetActiveWeightDegrees n D τ Q S
        rw [gaussianOffsetActiveWeightDegrees, Finset.mem_filter]
        refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hPbDegree),
          R', b, hbFace, ?_, rfl⟩
        simpa only [Pb] using hPb
      change Pb.natDegree ≤ H
      exact Finset.le_max' degrees Pb.natDegree hPbmem
  exact ⟨S, H, R, a, haFace, ell, hsource, hHle, hell, hstable, huniform⟩

/-- Signed source of an ADE atom key relative to the degree-`D` translation center `q`. -/
def gaussianAtomSignedSource (D q : ℕ) (ν : ℕ →₀ ℕ) : ℤ :=
  (ν.sum (fun i k => i * k) : ℤ) - ((D * q : ℕ) : ℤ)

/-- Every active atom at a Gaussian coefficient level belongs to exactly one of the four classes
needed by the tail argument: lower degree, larger top-degree source, least-source inside the
chosen centered window, or least-source exterior. -/
theorem activeAevalAtom_gaussian_four_way
    {n D τ q R : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} {S : ℤ}
    (ha : anchor ∈ Q.support)
    (haD : jetMonomialDegree n anchor = D)
    (haMax : ∀ m ∈ Q.support,
      jetMonomialDegree n m = D →
        magnitudeShiftCode n Q m ≤ magnitudeShiftCode n Q anchor)
    (hDmax : D = magnitudeMaxJetDegree n Q)
    (hS : S + (magnitudeShiftCode n Q anchor : ℤ) =
      ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ))
    {ν : ℕ →₀ ℕ}
    (hν : ν ∈ activeAevalAtoms n (D * q + τ) Q) :
    ν.sum (fun _ k => k) < D ∨
      (ν.sum (fun _ k => k) = D ∧ S < gaussianAtomSignedSource D q ν) ∨
      (ν.sum (fun _ k => k) = D ∧
        gaussianAtomSignedSource D q ν = S ∧ gaussianAtomInWindow q R ν) ∨
      (ν.sum (fun _ k => k) = D ∧
        gaussianAtomSignedSource D q ν = S ∧ ¬gaussianAtomInWindow q R ν) := by
  have happearing :
      ν ∈ (sigmaIdx n (D * q + τ) Q).image (atomKeyOf n) :=
    (mem_activeAevalAtoms.mp hν).1
  have hcountle : ν.sum (fun _ k => k) ≤ D := by
    simpa only [hDmax] using appearing_atom_count_le Q happearing
  rcases hcountle.eq_or_lt with hcount | hcountlt
  · obtain ⟨m, hm, hmDegree, hinvariant⟩ :=
      appearing_atom_sum_add_shiftCode Q happearing
    have hmTop : jetMonomialDegree n m = D := by
      rw [hmDegree, hcount]
    have hcode := haMax m hm hmTop
    have hsourceFloor : S ≤ gaussianAtomSignedSource D q ν := by
      have hinvariantInt :
          (ν.sum (fun i k => i * k) : ℤ) +
              (magnitudeShiftCode n Q m : ℤ) =
            ((D * q + τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ) := by
        exact_mod_cast hinvariant
      have hcodeInt :
          (magnitudeShiftCode n Q m : ℤ) ≤
            (magnitudeShiftCode n Q anchor : ℤ) := by
        exact_mod_cast hcode
      dsimp only [gaussianAtomSignedSource]
      push_cast at hinvariantInt hS ⊢
      nlinarith
    rcases hsourceFloor.eq_or_lt with hsource | hsource
    · by_cases hwindow : gaussianAtomInWindow q R ν
      · exact Or.inr (Or.inr (Or.inl ⟨hcount, hsource.symm, hwindow⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hcount, hsource.symm, hwindow⟩))
    · exact Or.inr (Or.inl ⟨hcount, hsource⟩)
  · exact Or.inl hcountlt

/-- Active lower-degree and larger-source atoms, the two aggregate classes which vanish after
normalization before the Gaussian exterior tail is considered. -/
def gaussianGapActiveAtoms
    (n D τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (S : ℤ) (q : ℕ) :
    Finset (ℕ →₀ ℕ) :=
  (activeAevalAtoms n (D * q + τ) Q).filter fun ν =>
    ν.sum (fun _ k => k) < D ∨ S < gaussianAtomSignedSource D q ν

/-- Active least-source atoms visible in the centered radius-`R` phase window. -/
def gaussianInteriorActiveAtoms
    (n D τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (S : ℤ)
    (q R : ℕ) : Finset (ℕ →₀ ℕ) := by
  classical
  exact (activeAevalAtoms n (D * q + τ) Q).filter fun ν =>
      ν.sum (fun _ k => k) = D ∧ gaussianAtomSignedSource D q ν = S ∧
        gaussianAtomInWindow q R ν

/-- Active least-source atoms outside the centered radius-`R` phase window. -/
def gaussianExteriorActiveAtoms
    (n D τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (S : ℤ)
    (q R : ℕ) : Finset (ℕ →₀ ℕ) := by
  classical
  exact (activeAevalAtoms n (D * q + τ) Q).filter fun ν =>
      ν.sum (fun _ k => k) = D ∧ gaussianAtomSignedSource D q ν = S ∧
        ¬gaussianAtomInWindow q R ν

/-- The active part of a finite centered Gaussian face is exactly the active least-source
interior class.  The reverse inclusion is constructive: an active atom is pulled back to its
intrinsic signed-offset pattern and then re-windowed. -/
theorem gaussianInteriorActiveAtoms_eq_filter_image_face
    {n D τ q R : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ} {S : ℤ}
    (hRq : R ≤ q) :
    gaussianInteriorActiveAtoms n D τ Q S q R =
      ((gaussianPolynomialPatternFace D S R).image
        (shiftedAtomPatternKey q R)).filter fun ν =>
          ν ∈ activeAevalAtoms n (D * q + τ) Q := by
  classical
  ext ν
  constructor
  · intro hν
    have hνData := Finset.mem_filter.mp hν
    have hactive : ν ∈ activeAevalAtoms n (D * q + τ) Q := hνData.1
    have hcount : ν.sum (fun _ k => k) = D := hνData.2.1
    have hsourceKey : gaussianAtomSignedSource D q ν = S := hνData.2.2.1
    have hwindow : gaussianAtomInWindow q R ν := hνData.2.2.2
    let a := gaussianOffsetPatternOfKey q ν
    have hsource : gaussianOffsetSource a = S := by
      dsimp only [a]
      have hcountZ : (ν.sum (fun _ k => k) : ℤ) = (D : ℤ) := by
        exact_mod_cast hcount
      rw [gaussianOffsetSource_patternOfKey, hcountZ]
      simpa only [gaussianAtomSignedSource, mul_comm] using hsourceKey
    have ha : a ∈ gaussianOffsetFace D S R :=
      gaussianOffsetPatternOfKey_mem_face hcount hsource hRq hwindow
    let p := gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R
    have hp : p ∈ gaussianPolynomialPatternFace D S R := by
      simpa only [p] using
        gaussianOffsetPatternWindow_mem_gaussianPolynomialPatternFace ha
    have hkey : shiftedAtomPatternKey q R p = ν := by
      calc
        shiftedAtomPatternKey q R p = gaussianOffsetShiftedKey q a := by
          simpa only [p] using shiftedAtomPatternKey_gaussianOffsetPatternWindow_eq ha hRq
        _ = ν := gaussianOffsetShiftedKey_patternOfKey q ν
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨p, hp, hkey⟩, hactive⟩
  · intro hν
    have hνData := Finset.mem_filter.mp hν
    obtain ⟨p, hp, hkey⟩ := Finset.mem_image.mp hνData.1
    have hpData := mem_gaussianPolynomialPatternFace.mp hp
    have hcount : ν.sum (fun _ k => k) = D := by
      rw [← hkey, shiftedAtomPatternKey_count, hpData.1]
    have hsource : gaussianAtomSignedSource D q ν = S := by
      rw [← hkey, gaussianAtomSignedSource]
      have hweighted := shiftedAtomPatternKey_weightedSum_eq
        (q := q) (K := R) p hpData.1
      have hweightedZ :
          (shiftedAtomPatternKey q R p).sum
              (fun i k => (i : ℤ) * (k : ℤ)) =
            ((D * (q - R) + ∑ j : Fin (2 * R + 1),
              (j : ℕ) * (p j : ℕ) : ℕ) : ℤ) := by
        exact_mod_cast hweighted
      rw [hweightedZ]
      change
        ((D * (q - R) + polynomialPatternSourceSum p : ℕ) : ℤ) -
            ((D * q : ℕ) : ℤ) = S
      push_cast
      rw [Nat.cast_sub hRq]
      nlinarith [hpData.2]
    have hwindow : gaussianAtomInWindow q R ν := by
      rw [← hkey]
      intro i hi
      have hiSupport : i ∈ (shiftedAtomPatternKey q R p).support :=
        Finsupp.mem_support_iff.mpr hi
      rw [shiftedAtomPatternKey,
        Finsupp.mapDomain_support_of_injective windowShift_injective] at hiSupport
      obtain ⟨r, hrSupport, rfl⟩ := Finset.mem_image.mp hiSupport
      have hrne : atomPatternKey p r ≠ 0 := Finsupp.mem_support_iff.mp hrSupport
      have hrlt : r < 2 * R + 1 := by
        by_contra hnot
        rw [atomPatternKey_apply, dif_neg hnot] at hrne
        exact hrne rfl
      simp only [windowShift]
      constructor <;> omega
    exact Finset.mem_filter.mpr
      ⟨hνData.2, hcount, hsource, hwindow⟩

/-- Enlarging the centered window can only move atoms from the exterior to the interior. -/
theorem gaussianExteriorActiveAtoms_subset_of_radius_le
    {n D τ q R K : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ} {S : ℤ}
    (hRK : R ≤ K) :
    gaussianExteriorActiveAtoms n D τ Q S q K ⊆
      gaussianExteriorActiveAtoms n D τ Q S q R := by
  classical
  intro ν hν
  have hνData := Finset.mem_filter.mp hν
  apply Finset.mem_filter.mpr
  refine ⟨hνData.1, hνData.2.1, hνData.2.2.1, ?_⟩
  intro hsmall
  apply hνData.2.2.2
  intro i hi
  have hiBounds := hsmall i hi
  constructor <;> omega

theorem aevalWeight_eq_zero_of_not_mem_activeAevalAtoms
    {n N : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ} {ν : ℕ →₀ ℕ}
    (hν : ν ∉ activeAevalAtoms n N Q) :
    aevalWeight n N Q ν = 0 := by
  by_contra hw
  exact hν (mem_activeAevalAtoms.mpr
    ⟨mem_appearingAtoms_of_aevalWeight_ne_zero hw, hw⟩)

/-- Exact three-class partition after selecting the least-source interior face.  The two gap
classes are kept in one finset so that their cancellations survive the later limit. -/
theorem activeAevalAtoms_sdiff_gaussianInterior_eq_gap_union_exterior
    {n D τ q R : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} {S : ℤ}
    (ha : anchor ∈ Q.support)
    (haD : jetMonomialDegree n anchor = D)
    (haMax : ∀ m ∈ Q.support,
      jetMonomialDegree n m = D →
        magnitudeShiftCode n Q m ≤ magnitudeShiftCode n Q anchor)
    (hDmax : D = magnitudeMaxJetDegree n Q)
    (hS : S + (magnitudeShiftCode n Q anchor : ℤ) =
      ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ)) :
    activeAevalAtoms n (D * q + τ) Q \
        gaussianInteriorActiveAtoms n D τ Q S q R =
      gaussianGapActiveAtoms n D τ Q S q ∪
        gaussianExteriorActiveAtoms n D τ Q S q R := by
  classical
  ext ν
  constructor
  · intro hν
    have hactive := (Finset.mem_sdiff.mp hν).1
    have hnotInterior := (Finset.mem_sdiff.mp hν).2
    rcases activeAevalAtom_gaussian_four_way
        ha haD haMax hDmax hS hactive with
      hlower | hlarger | hinterior | hexterior
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hactive, Or.inl hlower⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hactive, Or.inr hlarger.2⟩)
    · exact (hnotInterior
        (Finset.mem_filter.mpr ⟨hactive, hinterior⟩)).elim
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hactive, hexterior⟩)
  · intro hν
    rcases Finset.mem_union.mp hν with hgap | hexterior
    · have hgapData := Finset.mem_filter.mp hgap
      apply Finset.mem_sdiff.mpr
      refine ⟨hgapData.1, ?_⟩
      intro hinterior
      have hiData := (Finset.mem_filter.mp hinterior).2
      rcases hgapData.2 with hlower | hlarger
      · omega
      · omega
    · have heData := Finset.mem_filter.mp hexterior
      apply Finset.mem_sdiff.mpr
      refine ⟨heData.1, ?_⟩
      intro hinterior
      have hiData := (Finset.mem_filter.mp hinterior).2
      exact heData.2.2.2 hiData.2.2

/-- The gap and exterior classes are disjoint: exterior atoms have full degree and exactly the
least signed source. -/
theorem gaussianGapActiveAtoms_disjoint_gaussianExteriorActiveAtoms
    {n D τ q R : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ} {S : ℤ} :
    Disjoint (gaussianGapActiveAtoms n D τ Q S q)
      (gaussianExteriorActiveAtoms n D τ Q S q R) := by
  classical
  rw [Finset.disjoint_left]
  intro ν hgap hexterior
  have hgapData := (Finset.mem_filter.mp hgap).2
  have heData := (Finset.mem_filter.mp hexterior).2
  rcases hgapData with hlower | hlarger
  · omega
  · omega

/-- Lower degree has a quadratic gap and every larger active source has a linear Gaussian gap.
After taking their minimum, both classes have one common positive linear gap from a fixed
least-source witness. -/
theorem exists_eventually_gaussianGapActiveAtom_linear
    {B : ℝ} (hB : 0 < B)
    {n D τ : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} {S : ℤ} {R₀ : ℕ} {a₀ : ℤ →₀ ℕ}
    (ha : anchor ∈ Q.support)
    (haD : jetMonomialDegree n anchor = D)
    (haMax : ∀ m ∈ Q.support,
      jetMonomialDegree n m = D →
        magnitudeShiftCode n Q m ≤ magnitudeShiftCode n Q anchor)
    (hDmax : D = magnitudeMaxJetDegree n Q) (hD : 0 < D)
    (hS : S + (magnitudeShiftCode n Q anchor : ℤ) =
      ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ))
    (ha₀ : a₀ ∈ gaussianOffsetFace D S R₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℕ in atTop,
      ∀ ν ∈ gaussianGapActiveAtoms n D τ Q S (t + R₀),
        atomValuation (fun i => B * (i : ℝ) ^ 2)
            (gaussianOffsetShiftedKey (t + R₀) a₀) + c * (t : ℝ) ≤
          atomValuation (fun i => B * (i : ℝ) ^ 2) ν := by
  classical
  let p₀ := gaussianOffsetPatternWindow a₀
    (gaussianOffsetFace_totalCount ha₀) R₀
  have hp₀count : (∑ r, (p₀ r : ℕ)) = D := by
    simpa only [p₀] using gaussianOffsetPatternWindow_count ha₀
  have hkeyCount : (atomPatternKey p₀).sum (fun _ k => k) = D := by
    simpa only [atomPatternKey_count] using hp₀count
  let δ := tupleOfFinsupp (atomPatternKey p₀) D hkeyCount
  let Z := magnitudeMaxXDegree Q
  obtain ⟨cdeg, hcdeg, hdeg⟩ :=
    eventually_lowerDegree_tuplePower_rpow_gap
      (β := (2 : ℝ)) (by norm_num) hD δ Z
  let c := min (B * cdeg) B
  have hc : 0 < c := lt_min (mul_pos hB hcdeg) hB
  have hkeyShift : ∀ t : ℕ,
      key (fun i => t + δ i) = gaussianOffsetShiftedKey (t + R₀) a₀ := by
    intro t
    have hmap :
        Finsupp.mapDomain (fun r : ℕ => t + r) (key δ) =
          key (fun i => t + δ i) := by
      rw [key, key, Finsupp.mapDomain_finsetSum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finsupp.mapDomain_single]
    calc
      key (fun i => t + δ i) =
          Finsupp.mapDomain (fun r : ℕ => t + r) (key δ) := hmap.symm
      _ = Finsupp.mapDomain (windowShift (t + R₀) R₀)
          (atomPatternKey p₀) := by
        rw [key_tupleOfFinsupp (atomPatternKey p₀) D hkeyCount]
        apply congrArg (fun f : ℕ → ℕ =>
          Finsupp.mapDomain f (atomPatternKey p₀))
        funext r
        dsimp only [windowShift]
        omega
      _ = shiftedAtomPatternKey (t + R₀) R₀ p₀ := rfl
      _ = gaussianOffsetShiftedKey (t + R₀) a₀ :=
        shiftedAtomPatternKey_gaussianOffsetPatternWindow_eq ha₀ (by omega)
  have hE₀ : 0 ≤ gaussianOffsetPatternEnergy a₀ :=
    gaussianOffsetPatternEnergy_nonneg a₀
  refine ⟨c, hc, ?_⟩
  filter_upwards [hdeg,
    eventually_ge_atTop (max 1
      (max (magnitudeMaxXDegree Q + 1)
        (gaussianOffsetPatternEnergy a₀).toNat))] with t hdegT ht
  intro ν hνGap
  have hνActive : ν ∈ activeAevalAtoms n (D * (t + R₀) + τ) Q :=
    (Finset.mem_filter.mp hνGap).1
  have hνAppearing :
      ν ∈ (sigmaIdx n (D * (t + R₀) + τ) Q).image (atomKeyOf n) :=
    (mem_activeAevalAtoms.mp hνActive).1
  have hgapClass := (Finset.mem_filter.mp hνGap).2
  have ht1 : 1 ≤ t := (le_max_left 1 _).trans ht
  by_cases hlower : ν.sum (fun _ k => k) < D
  · let d := ν.sum (fun _ k => k)
    have hdD : d < D := by simpa only [d] using hlower
    have hlevel : magnitudeMaxXDegree Q < D * (t + R₀) + τ := by
      have htZ : magnitudeMaxXDegree Q + 1 ≤ t := by
        exact (le_trans (le_max_left _ _)
          (le_max_right 1 _)).trans ht
      have htD : t ≤ D * (t + R₀) + τ := by
        have hmul : t ≤ D * t := by
          simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ D by omega)
        nlinarith
      omega
    have hsupport := appearing_atom_support_nonempty_of_maxX_lt_level
      Q hνAppearing hlevel
    have hd : 0 < d := by
      by_contra hd0
      have hdEq : d = 0 := Nat.eq_zero_of_not_pos hd0
      obtain ⟨i, hi⟩ := hsupport
      have hiBound := finsupp_apply_le_count ν i
      have hiNe : ν i ≠ 0 := Finsupp.mem_support_iff.mp hi
      apply hiNe
      apply Nat.eq_zero_of_le_zero
      rw [← hdEq]
      simpa only [d] using hiBound
    let z := tupleOfFinsupp ν d (by rfl)
    have hsumz := sum_tupleOfFinsupp ν d (by rfl)
    have hmass : D * t ≤ (∑ i, z i) + Z := by
      rw [show (∑ i, z i) = ν.sum (fun i k => i * k) by
        simpa only [z] using hsumz]
      have hlowerMass := (appearing_atom_weighted_sum_bounds Q hνAppearing).1
      change D * (t + R₀) + τ - Z ≤ ν.sum (fun i k => i * k) at hlowerMass
      have hlevelZ : Z < D * (t + R₀) + τ := by
        simpa only [Z] using hlevel
      omega
    have hdegreeGap := hdegT d hd hdD z hmass
    have hbaseVal :
        (gaussianOffsetShiftedKey (t + R₀) a₀).sum
            (fun i k => (k : ℝ) * (i : ℝ) ^ (2 : ℝ)) =
          tuplePowerValuation (2 : ℝ) (fun i => t + δ i) := by
      rw [← hkeyShift t]
      exact phaseKeyPowerValuation (β := (2 : ℝ)) (fun i => t + δ i)
    have hνVal :
        ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ (2 : ℝ)) =
          tuplePowerValuation (2 : ℝ) z := by
      rw [valuation_tupleOfFinsupp ν d (by rfl)]
      rfl
    have hct : c * (t : ℝ) ≤ B * (cdeg * (t : ℝ) ^ (2 : ℝ)) := by
      have hcdegLe : c ≤ B * cdeg := min_le_left _ _
      have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
      have htSq : (t : ℝ) ≤ (t : ℝ) ^ (2 : ℝ) := by
        rw [Real.rpow_two]
        nlinarith
      calc
        c * (t : ℝ) ≤ (B * cdeg) * (t : ℝ) :=
          mul_le_mul_of_nonneg_right hcdegLe (by positivity)
        _ ≤ (B * cdeg) * (t : ℝ) ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_left htSq (mul_nonneg hB.le hcdeg.le)
        _ = B * (cdeg * (t : ℝ) ^ (2 : ℝ)) := by ring
    have hpowfun : (fun i : ℕ => B * (i : ℝ) ^ 2) =
        (fun i : ℕ => B * (i : ℝ) ^ (2 : ℝ)) := by
      funext i
      rw [Real.rpow_two]
    rw [hpowfun, atomValuation_scaledPower, atomValuation_scaledPower,
      hbaseVal, hνVal]
    nlinarith [mul_le_mul_of_nonneg_left hdegreeGap hB.le]
  · have hlarger : S < gaussianAtomSignedSource D (t + R₀) ν :=
      hgapClass.resolve_left hlower
    have hcountle : ν.sum (fun _ k => k) ≤ D := by
      simpa only [hDmax] using appearing_atom_count_le Q hνAppearing
    have hcount : ν.sum (fun _ k => k) = D :=
      le_antisymm hcountle (Nat.le_of_not_gt hlower)
    let T := gaussianAtomSignedSource D (t + R₀) ν
    have hST : S < T := by simpa only [T] using hlarger
    have hsource :
        gaussianOffsetSource (gaussianOffsetPatternOfKey (t + R₀) ν) = T := by
      have hcountZ : (ν.sum (fun _ k => k) : ℤ) = (D : ℤ) := by
        exact_mod_cast hcount
      rw [gaussianOffsetSource_patternOfKey, hcountZ]
      simp only [T, gaussianAtomSignedSource]
      ring
    have hνFormula := atomValuation_gaussianOffsetPatternOfKey B hcount hsource
    have hbaseFormula := atomValuation_gaussianOffsetShiftedKey B ha₀ (by omega)
    have henergyν :
        0 ≤ (gaussianOffsetPatternEnergy
          (gaussianOffsetPatternOfKey (t + R₀) ν) : ℝ) := by
      exact_mod_cast gaussianOffsetPatternEnergy_nonneg
        (gaussianOffsetPatternOfKey (t + R₀) ν)
    have henergy₀ :
        (gaussianOffsetPatternEnergy a₀ : ℝ) ≤ (t : ℝ) := by
      have htoNat : ((gaussianOffsetPatternEnergy a₀).toNat : ℤ) =
          gaussianOffsetPatternEnergy a₀ := Int.toNat_of_nonneg hE₀
      have htE : (gaussianOffsetPatternEnergy a₀).toNat ≤ t := by
        exact (le_trans (le_max_right _ _)
          (le_max_right 1 _)).trans ht
      exact_mod_cast (by omega : gaussianOffsetPatternEnergy a₀ ≤ (t : ℤ))
    have hsourceStep : (S : ℝ) + 1 ≤ (T : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hST)
    have hcB : c ≤ B := min_le_right _ _
    rw [hbaseFormula, hνFormula]
    nlinarith [mul_nonneg hB.le henergyν,
      mul_le_mul_of_nonneg_right hcB (by positivity : (0 : ℝ) ≤ t)]

/-- Coordinates actually used by a bounded multiplicity pattern. -/
def polynomialPatternSupport {M D : ℕ} (p : Fin M → Fin (D + 1)) : Finset (Fin M) :=
  Finset.univ.filter fun r => p r ≠ 0

/-- Largest absolute offset of an active pattern coordinate from the chosen center `K`. -/
def centeredPolynomialPatternRadius {M D : ℕ}
    (K : ℕ) (p : Fin M → Fin (D + 1)) : ℕ :=
  (polynomialPatternSupport p).sup fun r =>
    (((r : ℕ) : ℤ) - (K : ℤ)).natAbs

/-- A window representative of a global pattern supported in `[-R,R]` has centered support
radius at most `R`.  Thus the sharp grouped-weight bound is uniform over the whole radius-`R`
global face, despite the ambient window having length `2R+1`. -/
theorem centeredPolynomialPatternRadius_gaussianOffsetPatternWindow_le
    {D : ℕ} {S : ℤ} {R : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R) :
    centeredPolynomialPatternRadius R
        (gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R) ≤ R := by
  classical
  rw [centeredPolynomialPatternRadius]
  apply Finset.sup_le
  intro j hj
  have hjne :
      gaussianOffsetPatternWindow a (gaussianOffsetFace_totalCount ha) R j ≠ 0 :=
    (Finset.mem_filter.mp hj).2
  have hane : a ((centeredIndexEquiv R j).1) ≠ 0 := by
    intro hzero
    apply hjne
    apply Fin.ext
    exact hzero
  have hzsupport : (centeredIndexEquiv R j).1 ∈ a.support := by
    exact Finsupp.mem_support_iff.mpr hane
  have hzinterval := (mem_gaussianOffsetFace.mp ha).2.1 hzsupport
  simp only [gaussianOffsetInterval, Finset.mem_Icc] at hzinterval
  have habsInt :
      |((centeredIndexEquiv R j).1)| ≤ (R : ℤ) :=
    (abs_le).2 hzinterval
  have hnatCast :
      (((centeredIndexEquiv R j).1.natAbs : ℕ) : ℤ) ≤ (R : ℤ) := by
    rw [Int.natCast_natAbs]
    exact habsInt
  have hnat : (centeredIndexEquiv R j).1.natAbs ≤ R := by
    exact_mod_cast hnatCast
  simpa only [centeredIndexEquiv] using hnat

theorem atomPatternAssignment_mem_polynomialPatternSupport
    {M D : ℕ} {p : Fin M → Fin (D + 1)}
    {g : Fin D → Fin M} (hg : g ∈ atomPatternAssignments p) (t : Fin D) :
    g t ∈ polynomialPatternSupport p := by
  classical
  rw [polynomialPatternSupport, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hzero
  have hkey := mem_atomPatternAssignments.mp hg
  have hpos : key (fun j => (g j : ℕ)) (g t : ℕ) ≠ 0 := by
    rw [key_count_map]
    exact Multiset.count_ne_zero.mpr (by simp)
  apply hpos
  rw [hkey, atomPatternKey_apply]
  simp [hzero, (g t).isLt]

theorem polynomialPatternSupport_card_le_count
    {M D : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) :
    (polynomialPatternSupport p).card ≤ D := by
  classical
  calc
    (polynomialPatternSupport p).card =
        ∑ _r ∈ polynomialPatternSupport p, 1 := by simp
    _ ≤ ∑ r ∈ polynomialPatternSupport p, (p r : ℕ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrne : p r ≠ 0 := (Finset.mem_filter.mp hr).2
      have hrneNat : (p r : ℕ) ≠ 0 := by
        intro h
        apply hrne
        apply Fin.ext
        exact h
      omega
    _ ≤ ∑ r : Fin M, (p r : ℕ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro r _hr _hnot
        exact Nat.zero_le _
    _ = D := hcount

/-- The number of labelled assignments of a degree-`D` multiplicity pattern is bounded solely by
`D^D`, independently of the ambient window size. -/
theorem atomPatternAssignments_card_le_pow_count
    {M D : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) :
    (atomPatternAssignments p).card ≤ D ^ D := by
  classical
  let A := atomPatternAssignments p
  let S := polynomialPatternSupport p
  let encode : ↥A → (Fin D → ↥S) := fun g t =>
    ⟨g.1 t, atomPatternAssignment_mem_polynomialPatternSupport g.2 t⟩
  have hencode : Function.Injective encode := by
    intro g h hgh
    apply Subtype.ext
    funext t
    exact congrArg (fun e : Fin D → ↥S => (e t).1) hgh
  calc
    (atomPatternAssignments p).card = Fintype.card ↥A := by simp [A]
    _ ≤ Fintype.card (Fin D → ↥S) := Fintype.card_le_of_injective encode hencode
    _ = (polynomialPatternSupport p).card ^ D := by simp [S]
    _ ≤ D ^ D := Nat.pow_le_pow_left
      (polynomialPatternSupport_card_le_count p hcount) _

theorem assignment_centered_offset_le_radius
    {M D K : ℕ} {p : Fin M → Fin (D + 1)}
    {g : Fin D → Fin M} (hg : g ∈ atomPatternAssignments p) (t : Fin D) :
    ((((g t : Fin M) : ℕ) : ℤ) - (K : ℤ)).natAbs ≤
      centeredPolynomialPatternRadius K p := by
  exact Finset.le_sup (f := fun r : Fin M =>
    (((r : ℕ) : ℤ) - (K : ℤ)).natAbs)
      (atomPatternAssignment_mem_polynomialPatternSupport hg t)

theorem windowShift_assignment_le_center_add_radius
    {M D q K : ℕ} {p : Fin M → Fin (D + 1)}
    {g : Fin D → Fin M} (hg : g ∈ atomPatternAssignments p)
    (hKq : K ≤ q) (t : Fin D) :
    windowShift q K (g t : ℕ) ≤ q + centeredPolynomialPatternRadius K p := by
  have hoffNat := assignment_centered_offset_le_radius (K := K) hg t
  have hoffInt :
      |((((g t : Fin M) : ℕ) : ℤ) - (K : ℤ))| ≤
        (centeredPolynomialPatternRadius K p : ℤ) := by
    have hcast :
        ((((((g t : Fin M) : ℕ) : ℤ) - (K : ℤ)).natAbs : ℕ) : ℤ) ≤
          (centeredPolynomialPatternRadius K p : ℤ) := by
      exact_mod_cast hoffNat
    rw [Int.natCast_natAbs] at hcast
    exact hcast
  have hupper := (abs_le.mp hoffInt).2
  dsimp [windowShift]
  omega

/-- A labelled assignment whose contributing jet monomial has order at most `H` is bounded by
one common `H`-th power.  The estimate is uniform in the multiplicity pattern and in the window
offsets. -/
theorem norm_windowShift_descFactorial_prod_le
    {n D K τ M q H : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p))
    (g : Fin D → Fin M) (hKq : K ≤ q) (hq : 1 ≤ q)
    (horder : jetMonomialOrder n m.1 ≤ H) :
    ‖∏ t : Fin (jetMonomialDegree n m.1),
        ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤
      (((q + M) ^ H : ℕ) : ℝ) := by
  rw [norm_prod]
  have hfactor : ∀ t : Fin (jetMonomialDegree n m.1),
      ‖((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤
        ((((q + M) ^ (flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) := by
    intro t
    rw [Complex.norm_natCast]
    exact_mod_cast calc
      (windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t)
          ≤ (windowShift q K (g (polynomialPatternJetCast m t) : ℕ)) ^
              (flatOrder (fun j => m.1 j.succ) t) :=
            Nat.descFactorial_le_pow _ _
      _ ≤ (q + M) ^ (flatOrder (fun j => m.1 j.succ) t) := by
            apply Nat.pow_le_pow_left
            dsimp [windowShift]
            have hglt := (g (polynomialPatternJetCast m t)).isLt
            omega
  calc
    ∏ t, ‖((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
        ≤ ∏ t, ((((q + M) ^ (flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun t _ => hfactor t)
    _ = ((((q + M) ^
          (∑ t, flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) := by
      push_cast
      rw [← Finset.prod_pow_eq_pow_sum]
    _ ≤ (((q + M) ^ H : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) (by
        rw [flatOrder_sum]
        exact horder)

/-- Once an assignment is restricted to the support of a multiplicity pattern, its factorial
weight is controlled by the centered support radius rather than by the ambient window length.
This is the estimate which remains useful when the window itself grows with the translation
parameter. -/
theorem norm_windowShift_descFactorial_prod_le_centeredRadius
    {n D K τ M q H : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p))
    (g : Fin D → Fin M) (hg : g ∈ atomPatternAssignments p)
    (hKq : K ≤ q) (hq : 1 ≤ q)
    (horder : jetMonomialOrder n m.1 ≤ H) :
    ‖∏ t : Fin (jetMonomialDegree n m.1),
        ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤
      (((q + centeredPolynomialPatternRadius K p) ^ H : ℕ) : ℝ) := by
  rw [norm_prod]
  have hfactor : ∀ t : Fin (jetMonomialDegree n m.1),
      ‖((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤
        ((((q + centeredPolynomialPatternRadius K p) ^
          (flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) := by
    intro t
    rw [Complex.norm_natCast]
    exact_mod_cast calc
      (windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t)
          ≤ (windowShift q K (g (polynomialPatternJetCast m t) : ℕ)) ^
              (flatOrder (fun j => m.1 j.succ) t) :=
            Nat.descFactorial_le_pow _ _
      _ ≤ (q + centeredPolynomialPatternRadius K p) ^
          (flatOrder (fun j => m.1 j.succ) t) := by
            apply Nat.pow_le_pow_left
            exact windowShift_assignment_le_center_add_radius
              hg hKq (polynomialPatternJetCast m t)
  calc
    ∏ t, ‖((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
        ≤ ∏ t, ((((q + centeredPolynomialPatternRadius K p) ^
            (flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun t _ => hfactor t)
    _ = ((((q + centeredPolynomialPatternRadius K p) ^
          (∑ t, flatOrder (fun j => m.1 j.succ) t)) : ℕ) : ℝ) := by
      push_cast
      rw [← Finset.prod_pow_eq_pow_sum]
    _ ≤ (((q + centeredPolynomialPatternRadius K p) ^ H : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) (by
        rw [flatOrder_sum]
        exact horder)

/-- Every grouped bounded-pattern weight has a polynomial bound which is uniform over the
pattern.  The only window dependence is the explicit cardinal factor `M^D`; no coefficient-level
constant depends on the offsets. -/
theorem norm_eval_polynomialPatternWeightPoly_le
    {n D K τ M q H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) (hKq : K ≤ q) (hq : 1 ≤ q)
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ ≤
      magnitudeCoefficientMass Q * (((M ^ D : ℕ) : ℝ)) *
        (((q + M) ^ H : ℕ) : ℝ) := by
  classical
  rw [eval_polynomialPatternWeightPoly n D K τ Q p hKq]
  let A : ℝ := (((M ^ D : ℕ) : ℝ))
  let X : ℝ := (((q + M) ^ H : ℕ) : ℝ)
  have hcard : (atomPatternAssignments p).card ≤ M ^ D := by
    calc
      (atomPatternAssignments p).card ≤
          Fintype.card (Fin D → Fin M) := Finset.card_le_univ _
      _ = M ^ D := by simp
  have hinner : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      ‖∑ g ∈ atomPatternAssignments p,
          ∏ t : Fin (jetMonomialDegree n m.1),
            ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
              (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤ A * X := by
    intro m
    calc
      ‖∑ g ∈ atomPatternAssignments p,
          ∏ t : Fin (jetMonomialDegree n m.1),
            ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
              (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
          ≤ ∑ g ∈ atomPatternAssignments p,
              ‖∏ t : Fin (jetMonomialDegree n m.1),
                ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                  (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _g ∈ atomPatternAssignments p, X := by
        apply Finset.sum_le_sum
        intro g _hg
        exact norm_windowShift_descFactorial_prod_le m g hKq hq (horder m)
      _ = ((atomPatternAssignments p).card : ℝ) * X := by simp
      _ ≤ A * X := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [A]
          exact_mod_cast hcard
        · dsimp [X]
          positivity
  have hcoeff :
      (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
        ‖MvPolynomial.coeff m.1 Q‖) ≤ magnitudeCoefficientMass Q := by
    calc
      (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖) =
          ∑ m ∈ polynomialPatternJetGroup n D K τ Q p,
            ‖MvPolynomial.coeff m Q‖ :=
        by simpa using
          (Finset.sum_attach (polynomialPatternJetGroup n D K τ Q p)
            (fun m => ‖MvPolynomial.coeff m Q‖))
      _ ≤ ∑ m ∈ Q.support, ‖MvPolynomial.coeff m Q‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro m _hm _hnot
          positivity
      _ = magnitudeCoefficientMass Q := by rfl
  calc
    ‖∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
        MvPolynomial.coeff m.1 Q *
          ∑ g ∈ atomPatternAssignments p,
            ∏ t : Fin (jetMonomialDegree n m.1),
              ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
        ≤ ∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
            ‖MvPolynomial.coeff m.1 Q *
              ∑ g ∈ atomPatternAssignments p,
                ∏ t : Fin (jetMonomialDegree n m.1),
                  ((windowShift q K
                    (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                    (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖ * (A * X) := by
      apply Finset.sum_le_sum
      intro m _hm
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hinner m) (norm_nonneg _)
    _ = (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖) * (A * X) := by
      rw [Finset.sum_mul]
    _ ≤ magnitudeCoefficientMass Q * (A * X) :=
      mul_le_mul_of_nonneg_right hcoeff (by dsimp [A, X]; positivity)
    _ = magnitudeCoefficientMass Q * (((M ^ D : ℕ) : ℝ)) *
          (((q + M) ^ H : ℕ) : ℝ) := by
      dsimp [A, X]
      ring

/-- The grouped weight of a degree-`D` pattern is bounded using only its centered support radius.
The ambient window cardinality has disappeared: the assignment count is at most `D^D`, because
every labelled atom must land in the at-most-`D` active support positions. -/
theorem norm_eval_polynomialPatternWeightPoly_le_centeredRadius
    {n D K τ M q H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hKq : K ≤ q) (hq : 1 ≤ q)
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ ≤
      magnitudeCoefficientMass Q * (((D ^ D : ℕ) : ℝ)) *
        (((q + centeredPolynomialPatternRadius K p) ^ H : ℕ) : ℝ) := by
  classical
  rw [eval_polynomialPatternWeightPoly n D K τ Q p hKq]
  let A : ℝ := (((D ^ D : ℕ) : ℝ))
  let X : ℝ := (((q + centeredPolynomialPatternRadius K p) ^ H : ℕ) : ℝ)
  have hcard : (atomPatternAssignments p).card ≤ D ^ D :=
    atomPatternAssignments_card_le_pow_count p hcount
  have hinner : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      ‖∑ g ∈ atomPatternAssignments p,
          ∏ t : Fin (jetMonomialDegree n m.1),
            ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
              (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ ≤ A * X := by
    intro m
    calc
      ‖∑ g ∈ atomPatternAssignments p,
          ∏ t : Fin (jetMonomialDegree n m.1),
            ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
              (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
          ≤ ∑ g ∈ atomPatternAssignments p,
              ‖∏ t : Fin (jetMonomialDegree n m.1),
                ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                  (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _g ∈ atomPatternAssignments p, X := by
        apply Finset.sum_le_sum
        intro g hg
        exact norm_windowShift_descFactorial_prod_le_centeredRadius
          m g hg hKq hq (horder m)
      _ = ((atomPatternAssignments p).card : ℝ) * X := by simp
      _ ≤ A * X := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [A]
          exact_mod_cast hcard
        · dsimp [X]
          positivity
  have hcoeff :
      (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
        ‖MvPolynomial.coeff m.1 Q‖) ≤ magnitudeCoefficientMass Q := by
    calc
      (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖) =
          ∑ m ∈ polynomialPatternJetGroup n D K τ Q p,
            ‖MvPolynomial.coeff m Q‖ :=
        by simpa using
          (Finset.sum_attach (polynomialPatternJetGroup n D K τ Q p)
            (fun m => ‖MvPolynomial.coeff m Q‖))
      _ ≤ ∑ m ∈ Q.support, ‖MvPolynomial.coeff m Q‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro m _hm _hnot
          positivity
      _ = magnitudeCoefficientMass Q := by rfl
  calc
    ‖∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
        MvPolynomial.coeff m.1 Q *
          ∑ g ∈ atomPatternAssignments p,
            ∏ t : Fin (jetMonomialDegree n m.1),
              ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖
        ≤ ∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
            ‖MvPolynomial.coeff m.1 Q *
              ∑ g ∈ atomPatternAssignments p,
                ∏ t : Fin (jetMonomialDegree n m.1),
                  ((windowShift q K
                    (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                    (flatOrder (fun j => m.1 j.succ) t) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖ * (A * X) := by
      apply Finset.sum_le_sum
      intro m _hm
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hinner m) (norm_nonneg _)
    _ = (∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
          ‖MvPolynomial.coeff m.1 Q‖) * (A * X) := by
      rw [Finset.sum_mul]
    _ ≤ magnitudeCoefficientMass Q * (A * X) :=
      mul_le_mul_of_nonneg_right hcoeff (by dsimp [A, X]; positivity)
    _ = magnitudeCoefficientMass Q * (((D ^ D : ℕ) : ℝ)) *
          (((q + centeredPolynomialPatternRadius K p) ^ H : ℕ) : ℝ) := by
      dsimp [A, X]
      ring

/-- The maximal jet order is a valid common coefficient-level degree bound for every grouped
pattern weight. -/
theorem norm_eval_polynomialPatternWeightPoly_le_maxJetOrder
    {n D K τ M q : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) (hKq : K ≤ q) (hq : 1 ≤ q) :
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ ≤
      magnitudeCoefficientMass Q * (((M ^ D : ℕ) : ℝ)) *
        (((q + M) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) := by
  apply norm_eval_polynomialPatternWeightPoly_le Q p hKq hq
  intro m
  exact jetOrder_le_magnitudeMaxJetOrder Q
    (Finset.mem_filter.mp m.2).1

/-- If `H` bounds the order of every monomial active in one source group, division by `q^H`
leaves a bound polynomial only in the window size. -/
theorem norm_eval_polynomialPatternWeightPoly_div_pow_le_of_order_le
    {n D K τ M q H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) (hKq : K ≤ q) (hq : 1 ≤ q)
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) /
        (q : ℂ) ^ H‖ ≤
      magnitudeCoefficientMass Q * (((M + 1) ^ (D + H) : ℕ) : ℝ) := by
  let C : ℝ := magnitudeCoefficientMass Q * (((M ^ D : ℕ) : ℝ))
  let qH : ℝ := (((q ^ H : ℕ) : ℝ))
  let MH : ℝ := ((((M + 1) ^ H : ℕ) : ℝ))
  have hraw : ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ ≤
      C * (((q + M) ^ H : ℕ) : ℝ) := by
    simpa only [C, mul_assoc] using
      norm_eval_polynomialPatternWeightPoly_le Q p hKq hq horder
  have hbase : q + M ≤ q * (M + 1) := by
    nlinarith [Nat.zero_le M]
  have hpow : (q + M) ^ H ≤ q ^ H * (M + 1) ^ H := by
    calc
      (q + M) ^ H ≤ (q * (M + 1)) ^ H := Nat.pow_le_pow_left hbase _
      _ = q ^ H * (M + 1) ^ H := by rw [mul_pow]
  have hqHpos : 0 < qH := by
    dsimp [qH]
    positivity
  have hratio : ((((q + M) ^ H : ℕ) : ℝ)) / qH ≤ MH := by
    apply (div_le_iff₀ hqHpos).2
    dsimp [qH, MH]
    exact_mod_cast (by simpa [mul_comm] using hpow)
  have hC : 0 ≤ C := by
    dsimp [C, magnitudeCoefficientMass]
    positivity
  rw [norm_div, norm_pow, Complex.norm_natCast]
  rw [show (q : ℝ) ^ H = qH by
    dsimp [qH]
    push_cast
    rfl]
  change _ / qH ≤ _
  calc
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ / qH
        ≤ (C * (((q + M) ^ H : ℕ) : ℝ)) / qH :=
      div_le_div_of_nonneg_right hraw hqHpos.le
    _ = C * (((((q + M) ^ H : ℕ) : ℝ)) / qH) := by ring
    _ ≤ C * MH := mul_le_mul_of_nonneg_left hratio hC
    _ ≤ magnitudeCoefficientMass Q *
        (((M + 1) ^ (D + H) : ℕ) : ℝ) := by
      dsimp [C, MH]
      have hMD : M ^ D ≤ (M + 1) ^ D :=
        Nat.pow_le_pow_left (Nat.le_succ M) _
      have hmass : 0 ≤ magnitudeCoefficientMass Q := by
        dsimp [magnitudeCoefficientMass]
        positivity
      have hcast : ((M ^ D : ℕ) : ℝ) ≤ (((M + 1) ^ D : ℕ) : ℝ) := by
        exact_mod_cast hMD
      calc
        magnitudeCoefficientMass Q * ((M ^ D : ℕ) : ℝ) *
            (((M + 1) ^ H : ℕ) : ℝ)
            ≤ magnitudeCoefficientMass Q * (((M + 1) ^ D : ℕ) : ℝ) *
              (((M + 1) ^ H : ℕ) : ℝ) := by
          gcongr
        _ = magnitudeCoefficientMass Q *
            (((M + 1) ^ (D + H) : ℕ) : ℝ) := by
          push_cast
          rw [pow_add]
          ring

/-- After maximal-order normalization, a degree-`D` pattern has a bound depending only on its
centered support radius.  In particular, enlarging the ambient centered window does not enlarge
the bound for a fixed global offset pattern. -/
theorem norm_eval_polynomialPatternWeightPoly_div_pow_le_centeredRadius_of_order_le
    {n D K τ M q H : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hKq : K ≤ q) (hq : 1 ≤ q)
    (horder : ∀ m : ↥(polynomialPatternJetGroup n D K τ Q p),
      jetMonomialOrder n m.1 ≤ H) :
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) /
        (q : ℂ) ^ H‖ ≤
      magnitudeCoefficientMass Q * (((D ^ D : ℕ) : ℝ)) *
        (((centeredPolynomialPatternRadius K p + 1) ^ H : ℕ) : ℝ) := by
  let C : ℝ := magnitudeCoefficientMass Q * (((D ^ D : ℕ) : ℝ))
  let R : ℕ := centeredPolynomialPatternRadius K p
  let qH : ℝ := (((q ^ H : ℕ) : ℝ))
  let RH : ℝ := ((((R + 1) ^ H : ℕ) : ℝ))
  have hraw : ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ ≤
      C * (((q + R) ^ H : ℕ) : ℝ) := by
    simpa only [C, R, mul_assoc] using
      norm_eval_polynomialPatternWeightPoly_le_centeredRadius
        Q p hcount hKq hq horder
  have hbase : q + R ≤ q * (R + 1) := by
    nlinarith [Nat.zero_le R]
  have hpow : (q + R) ^ H ≤ q ^ H * (R + 1) ^ H := by
    calc
      (q + R) ^ H ≤ (q * (R + 1)) ^ H := Nat.pow_le_pow_left hbase _
      _ = q ^ H * (R + 1) ^ H := by rw [mul_pow]
  have hqHpos : 0 < qH := by
    dsimp [qH]
    positivity
  have hratio : ((((q + R) ^ H : ℕ) : ℝ)) / qH ≤ RH := by
    apply (div_le_iff₀ hqHpos).2
    dsimp [qH, RH]
    exact_mod_cast (by simpa [mul_comm] using hpow)
  have hC : 0 ≤ C := by
    dsimp [C, magnitudeCoefficientMass]
    positivity
  rw [norm_div, norm_pow, Complex.norm_natCast]
  rw [show (q : ℝ) ^ H = qH by
    dsimp [qH]
    push_cast
    rfl]
  change _ / qH ≤ _
  calc
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ)‖ / qH
        ≤ (C * (((q + R) ^ H : ℕ) : ℝ)) / qH :=
      div_le_div_of_nonneg_right hraw hqHpos.le
    _ = C * (((((q + R) ^ H : ℕ) : ℝ)) / qH) := by ring
    _ ≤ C * RH := mul_le_mul_of_nonneg_left hratio hC
    _ = magnitudeCoefficientMass Q * (((D ^ D : ℕ) : ℝ)) *
        (((centeredPolynomialPatternRadius K p + 1) ^ H : ℕ) : ℝ) := by
      dsimp [C, R, RH]

/-- After division by the common maximal-order power, every grouped weight is bounded by one
fixed polynomial in the window size.  This is the uniform estimate required before the Gaussian
lattice tail is summed. -/
theorem norm_eval_polynomialPatternWeightPoly_div_pow_le
    {n D K τ M q : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (p : Fin M → Fin (D + 1)) (hKq : K ≤ q) (hq : 1 ≤ q) :
    ‖(polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) /
        (q : ℂ) ^ magnitudeMaxJetOrder n Q‖ ≤
      magnitudeCoefficientMass Q *
        (((M + 1) ^ (D + magnitudeMaxJetOrder n Q) : ℕ) : ℝ) := by
  apply norm_eval_polynomialPatternWeightPoly_div_pow_le_of_order_le Q p hKq hq
  intro m
  exact jetOrder_le_magnitudeMaxJetOrder Q
    (Finset.mem_filter.mp m.2).1

/-! ## Cancellation-safe interpolation bounds -/

/-- The fixed interpolation nodes used to recover all coefficients of a polynomial whose degree
is at most `J`.  They do not depend on the Gaussian window radius. -/
def gaussianLagrangeNodes (J : ℕ) : Fin (J + 1) → ℂ :=
  fun i => ((i : ℕ) : ℂ)

theorem gaussianLagrangeNodes_injective (J : ℕ) :
    Function.Injective (gaussianLagrangeNodes J) := by
  intro i j hij
  apply Fin.ext
  change (((i : ℕ) : ℂ)) = (((j : ℕ) : ℂ)) at hij
  exact_mod_cast hij

/-- A symbolic, finite coefficient mass for interpolation in degree at most `J`.  Keeping this
constant unevaluated is important: the Gaussian argument needs only finiteness and nonnegativity,
not a numerical estimate. -/
noncomputable def gaussianLagrangeCoefficientMass (J : ℕ) : ℝ :=
  ∑ h ∈ Finset.range (J + 1),
    ∑ i : Fin (J + 1),
      ‖(Lagrange.basis Finset.univ (gaussianLagrangeNodes J) i).coeff h‖

theorem gaussianLagrangeCoefficientMass_nonneg (J : ℕ) :
    0 ≤ gaussianLagrangeCoefficientMass J := by
  unfold gaussianLagrangeCoefficientMass
  positivity

/-- Coefficient form of interpolation at the fixed nodes `0, ..., J`. -/
theorem coeff_eq_sum_gaussianLagrange
    (J : ℕ) (P : ℂ[X]) (hP : P.natDegree ≤ J) (h : ℕ) :
    P.coeff h = ∑ i : Fin (J + 1),
      P.eval (gaussianLagrangeNodes J i) *
        (Lagrange.basis Finset.univ (gaussianLagrangeNodes J) i).coeff h := by
  have hdegree : P.degree <
      ((Finset.univ : Finset (Fin (J + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    calc
      P.degree ≤ (P.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (J : WithBot ℕ) := WithBot.coe_le_coe.mpr hP
      _ < ((J + 1 : ℕ) : WithBot ℕ) := by norm_cast; omega
  have hinterp := Lagrange.eq_interpolate
    (s := (Finset.univ : Finset (Fin (J + 1))))
    (v := gaussianLagrangeNodes J)
    (gaussianLagrangeNodes_injective J).injOn hdegree
  have hc := congrArg (fun Q : ℂ[X] => Q.coeff h) hinterp
  rw [Lagrange.interpolate_apply] at hc
  change P.coeff h = (Polynomial.lcoeff ℂ h)
    (∑ i, Polynomial.C (P.eval (gaussianLagrangeNodes J i)) *
      Lagrange.basis Finset.univ (gaussianLagrangeNodes J) i) at hc
  rw [map_sum] at hc
  change P.coeff h = ∑ i,
    (Polynomial.C (P.eval (gaussianLagrangeNodes J i)) *
      Lagrange.basis Finset.univ (gaussianLagrangeNodes J) i).coeff h at hc
  simp only [Polynomial.coeff_C_mul] at hc
  simpa [mul_comm] using hc

/-- Every coefficient of a degree-at-most-`J` polynomial is controlled by the common bound on
its `J+1` fixed samples. -/
theorem norm_coeff_le_gaussianLagrangeCoefficientMass_mul
    (J : ℕ) (P : ℂ[X]) (hP : P.natDegree ≤ J)
    (B : ℝ) (hB : 0 ≤ B)
    (hsample : ∀ i : Fin (J + 1),
      ‖P.eval (gaussianLagrangeNodes J i)‖ ≤ B)
    {h : ℕ} (hh : h ≤ J) :
    ‖P.coeff h‖ ≤ gaussianLagrangeCoefficientMass J * B := by
  have hsingle :
      (∑ i : Fin (J + 1),
          ‖(Lagrange.basis Finset.univ
            (gaussianLagrangeNodes J) i).coeff h‖) ≤
        gaussianLagrangeCoefficientMass J := by
    rw [gaussianLagrangeCoefficientMass]
    exact Finset.single_le_sum
      (fun k _hk => Finset.sum_nonneg fun _i _hi => norm_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hh))
  calc
    ‖P.coeff h‖ = ‖∑ i : Fin (J + 1),
        P.eval (gaussianLagrangeNodes J i) *
          (Lagrange.basis Finset.univ
            (gaussianLagrangeNodes J) i).coeff h‖ :=
      congrArg norm (coeff_eq_sum_gaussianLagrange J P hP h)
    _ ≤ ∑ i : Fin (J + 1),
        ‖P.eval (gaussianLagrangeNodes J i) *
          (Lagrange.basis Finset.univ
            (gaussianLagrangeNodes J) i).coeff h‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (J + 1),
        ‖(Lagrange.basis Finset.univ
          (gaussianLagrangeNodes J) i).coeff h‖ * B := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_mul]
      calc
        ‖P.eval (gaussianLagrangeNodes J i)‖ *
            ‖(Lagrange.basis Finset.univ
              (gaussianLagrangeNodes J) i).coeff h‖ =
          ‖(Lagrange.basis Finset.univ
              (gaussianLagrangeNodes J) i).coeff h‖ *
            ‖P.eval (gaussianLagrangeNodes J i)‖ := by ring
        _ ≤ ‖(Lagrange.basis Finset.univ
              (gaussianLagrangeNodes J) i).coeff h‖ * B :=
          mul_le_mul_of_nonneg_left (hsample i) (norm_nonneg _)
    _ = (∑ i : Fin (J + 1),
          ‖(Lagrange.basis Finset.univ
            (gaussianLagrangeNodes J) i).coeff h‖) * B := by
      rw [Finset.sum_mul]
    _ ≤ gaussianLagrangeCoefficientMass J * B :=
      mul_le_mul_of_nonneg_right hsingle hB

/-- Translate the argument of a polynomial by the nonnegative integer `K`. -/
def gaussianPolynomialTranslate (K : ℕ) (P : ℂ[X]) : ℂ[X] :=
  P.comp (Polynomial.X + Polynomial.C (K : ℂ))

theorem eval_gaussianPolynomialTranslate
    (K : ℕ) (P : ℂ[X]) (x : ℂ) :
    (gaussianPolynomialTranslate K P).eval x = P.eval (x + (K : ℂ)) := by
  simp [gaussianPolynomialTranslate, Polynomial.eval_comp]

theorem natDegree_gaussianPolynomialTranslate_le
    (K : ℕ) (P : ℂ[X]) :
    (gaussianPolynomialTranslate K P).natDegree ≤ P.natDegree := by
  rw [gaussianPolynomialTranslate]
  calc
    (P.comp (Polynomial.X + Polynomial.C (K : ℂ))).natDegree ≤
        P.natDegree *
          (Polynomial.X + Polynomial.C (K : ℂ)).natDegree :=
      Polynomial.natDegree_comp_le
    _ = P.natDegree := by
      rw [Polynomial.natDegree_X_add_C, mul_one]

/-- Fixed-node interpolation after translating the sampling interval to start at `K`. -/
theorem norm_coeff_gaussianPolynomialTranslate_le
    (J K : ℕ) (P : ℂ[X]) (hP : P.natDegree ≤ J)
    (B : ℝ) (hB : 0 ≤ B)
    (hsample : ∀ i : Fin (J + 1),
      ‖P.eval ((K + (i : ℕ) : ℕ) : ℂ)‖ ≤ B)
    {h : ℕ} (hh : h ≤ J) :
    ‖(gaussianPolynomialTranslate K P).coeff h‖ ≤
      gaussianLagrangeCoefficientMass J * B := by
  apply norm_coeff_le_gaussianLagrangeCoefficientMass_mul J
    (gaussianPolynomialTranslate K P)
    ((natDegree_gaussianPolynomialTranslate_le K P).trans hP)
    B hB
  · intro i
    rw [eval_gaussianPolynomialTranslate]
    simpa [gaussianLagrangeNodes, Nat.cast_add, add_comm] using hsample i
  · exact hh

/-- If every coefficient of the translated polynomial through degree `H` has norm at most `C`,
then division by the attained degree `q^H` is uniformly bounded.  This lemma is deliberately
coefficient-based: it remains valid when higher-order jet monomials cancel from the grouped
weight polynomial. -/
theorem norm_eval_div_pow_le_of_translate_coeff_bound
    (P : ℂ[X]) {K q H : ℕ} (hP : P.natDegree ≤ H)
    (hKq : K ≤ q) (hq : 1 ≤ q)
    (C : ℝ) (hC : 0 ≤ C)
    (hcoeff : ∀ h ≤ H,
      ‖(gaussianPolynomialTranslate K P).coeff h‖ ≤ C) :
    ‖P.eval (q : ℂ) / (q : ℂ) ^ H‖ ≤ ((H + 1 : ℕ) : ℝ) * C := by
  let T := gaussianPolynomialTranslate K P
  let s := q - K
  let qH : ℝ := ((q ^ H : ℕ) : ℝ)
  have hT : T.natDegree ≤ H := by
    exact (natDegree_gaussianPolynomialTranslate_le K P).trans hP
  have heval : T.eval (s : ℂ) = P.eval (q : ℂ) := by
    dsimp only [T]
    rw [eval_gaussianPolynomialTranslate]
    congr 1
    dsimp only [s]
    exact_mod_cast Nat.sub_add_cancel hKq
  have hpow : ∀ h ≤ H, ((s ^ h : ℕ) : ℝ) ≤ qH := by
    intro h hh
    dsimp only [s, qH]
    exact_mod_cast calc
      (q - K) ^ h ≤ q ^ h := Nat.pow_le_pow_left (Nat.sub_le q K) _
      _ ≤ q ^ H := Nat.pow_le_pow_right hq hh
  have hevalBound : ‖T.eval (s : ℂ)‖ ≤
      ((H + 1 : ℕ) : ℝ) * C * qH := by
    rw [Polynomial.eval_eq_sum_range'
      (n := H + 1) (Nat.lt_succ_of_le hT)]
    calc
      ‖∑ h ∈ Finset.range (H + 1), T.coeff h * (s : ℂ) ^ h‖ ≤
          ∑ h ∈ Finset.range (H + 1),
            ‖T.coeff h * (s : ℂ) ^ h‖ := norm_sum_le _ _
      _ ≤ ∑ _h ∈ Finset.range (H + 1), C * qH := by
        apply Finset.sum_le_sum
        intro h hh
        have hhH : h ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
        rw [norm_mul, norm_pow, Complex.norm_natCast]
        exact mul_le_mul (hcoeff h hhH)
          (by simpa only [Nat.cast_pow] using hpow h hhH)
          (by positivity) hC
      _ = ((H + 1 : ℕ) : ℝ) * C * qH := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
  have hqHpos : 0 < qH := by
    dsimp only [qH]
    positivity
  rw [norm_div, norm_pow, Complex.norm_natCast, ← heval]
  have hqH_eq : (q : ℝ) ^ H = qH := by
    dsimp only [qH]
    rw [Nat.cast_pow]
  rw [hqH_eq]
  change ‖T.eval (s : ℂ)‖ / qH ≤ ((H + 1 : ℕ) : ℝ) * C
  exact (div_le_iff₀ hqHpos).2 (by
    simpa [mul_assoc] using hevalBound)

/-- The fixed ADE-dependent constant in the cancellation-safe Gaussian grouped-weight bound. -/
noncomputable def gaussianPatternWeightNormalizationConstant
    (n D : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) : ℝ :=
  let J := magnitudeMaxJetOrder n Q
  ((J + 1 : ℕ) : ℝ) * gaussianLagrangeCoefficientMass J *
    magnitudeCoefficientMass Q * (((D ^ D : ℕ) : ℝ)) *
      ((((J + 2) ^ J : ℕ) : ℝ))

theorem gaussianPatternWeightNormalizationConstant_nonneg
    (n D : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    0 ≤ gaussianPatternWeightNormalizationConstant n D Q := by
  have hmass : 0 ≤ magnitudeCoefficientMass Q := by
    unfold magnitudeCoefficientMass
    positivity
  unfold gaussianPatternWeightNormalizationConstant
  positivity

/-- Cancellation-safe uniform bound for every global pattern on a centered Gaussian face.  The
normalizing exponent `H` need only bound the *attained polynomial degree*; active jet monomials
may have larger order and cancel. -/
theorem norm_eval_gaussianOffsetPatternWeight_div_pow_le
    {n D τ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {S : ℤ} {R H q : ℕ} {a : ℤ →₀ ℕ}
    (ha : a ∈ gaussianOffsetFace D S R)
    (hdegree :
      (polynomialPatternWeightPoly n D R τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount ha) R)).natDegree ≤ H)
    (hHJ : H ≤ magnitudeMaxJetOrder n Q)
    (hRq : R + 1 ≤ q) :
    ‖(polynomialPatternWeightPoly n D R τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount ha) R)).eval (q : ℂ) /
          (q : ℂ) ^ H‖ ≤
      gaussianPatternWeightNormalizationConstant n D Q *
        ((((R + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ)) := by
  classical
  let J := magnitudeMaxJetOrder n Q
  let p := gaussianOffsetPatternWindow a
    (gaussianOffsetFace_totalCount ha) R
  let P := polynomialPatternWeightPoly n D R τ Q p
  let B : ℝ := magnitudeCoefficientMass Q * (((D ^ D : ℕ) : ℝ)) *
    (((((J + 2) * (R + 1)) ^ J : ℕ) : ℝ))
  have hPJ : P.natDegree ≤ J := by
    exact hdegree.trans hHJ
  have hB : 0 ≤ B := by
    dsimp only [B, magnitudeCoefficientMass]
    positivity
  have hpcount : (∑ r, (p r : ℕ)) = D := by
    simpa only [p] using gaussianOffsetPatternWindow_count ha
  have hpradius : centeredPolynomialPatternRadius R p ≤ R := by
    simpa only [p] using centeredPolynomialPatternRadius_gaussianOffsetPatternWindow_le ha
  have hsample : ∀ i : Fin (J + 1),
      ‖P.eval ((R + 1 + (i : ℕ) : ℕ) : ℂ)‖ ≤ B := by
    intro i
    let qi := R + 1 + (i : ℕ)
    have hRqi : R ≤ qi := by dsimp only [qi]; omega
    have hqi : 1 ≤ qi := by dsimp only [qi]; omega
    have hiJ : (i : ℕ) ≤ J := Nat.le_of_lt_succ i.isLt
    have hbase : qi + centeredPolynomialPatternRadius R p ≤
        (J + 2) * (R + 1) := by
      dsimp only [qi]
      nlinarith [Nat.zero_le (J * R)]
    have hraw := norm_eval_polynomialPatternWeightPoly_le_centeredRadius
      (n := n) (D := D) (K := R) (τ := τ) (M := 2 * R + 1)
      (q := qi) (H := J) Q p hpcount hRqi hqi
      (fun m => jetOrder_le_magnitudeMaxJetOrder Q
        (Finset.mem_filter.mp m.2).1)
    change ‖P.eval (qi : ℂ)‖ ≤ B
    calc
      ‖P.eval (qi : ℂ)‖ ≤
          magnitudeCoefficientMass Q * (((D ^ D : ℕ) : ℝ)) *
            ((((qi + centeredPolynomialPatternRadius R p) ^ J : ℕ) : ℝ)) :=
        hraw
      _ ≤ magnitudeCoefficientMass Q * (((D ^ D : ℕ) : ℝ)) *
            (((((J + 2) * (R + 1)) ^ J : ℕ) : ℝ)) := by
        gcongr
        exact_mod_cast Nat.pow_le_pow_left hbase J
      _ = B := by rfl
  have htranslated : ∀ h ≤ H,
      ‖(gaussianPolynomialTranslate (R + 1) P).coeff h‖ ≤
        gaussianLagrangeCoefficientMass J * B := by
    intro h hh
    exact norm_coeff_gaussianPolynomialTranslate_le J (R + 1) P hPJ B hB
      (by simpa only [add_assoc] using hsample) (hh.trans hHJ)
  have hnormalized := norm_eval_div_pow_le_of_translate_coeff_bound
    P hdegree hRq (by omega)
      (gaussianLagrangeCoefficientMass J * B)
      (mul_nonneg (gaussianLagrangeCoefficientMass_nonneg J) hB)
      htranslated
  change ‖P.eval (q : ℂ) / (q : ℂ) ^ H‖ ≤ _
  calc
    ‖P.eval (q : ℂ) / (q : ℂ) ^ H‖ ≤
        ((H + 1 : ℕ) : ℝ) *
          (gaussianLagrangeCoefficientMass J * B) := hnormalized
    _ ≤ ((J + 1 : ℕ) : ℝ) *
          (gaussianLagrangeCoefficientMass J * B) := by
      gcongr
      exact_mod_cast Nat.add_le_add_right hHJ 1
    _ = gaussianPatternWeightNormalizationConstant n D Q *
          ((((R + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ)) := by
      dsimp only [B, J, gaussianPatternWeightNormalizationConstant]
      push_cast
      rw [mul_pow]
      ring

/-! ## Canonical tuple encoding of multiplicity patterns -/

/-- Multiplicity pattern of an integer offset tuple. -/
noncomputable def integerTupleKey {D : ℕ} (z : Fin D → ℤ) : ℤ →₀ ℕ :=
  ∑ i, Finsupp.single (z i) 1

theorem integerTupleKey_count_map {D : ℕ} (z : Fin D → ℤ) (r : ℤ) :
    integerTupleKey z r =
      Multiset.count r (Multiset.map z Finset.univ.val) := by
  rw [integerTupleKey]
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val,
    Finset.card_filter]
  simp only [eq_comm]

/-- Canonical ordered tuple listing the entries of a finite integer multiplicity pattern. -/
noncomputable def integerTupleOfFinsupp (a : ℤ →₀ ℕ) (D : ℕ)
    (hcount : a.sum (fun _ k => k) = D) : Fin D → ℤ :=
  let m := Finsupp.toMultiset a
  let hcard : Fintype.card m = D := by
    rw [Multiset.card_coe, Finsupp.card_toMultiset]
    simpa [Function.id_def] using hcount
  let e : Fin D ≃ m := (Fintype.equivFinOfCardEq hcard).symm
  fun i => (e i : ℤ)

theorem integerTupleKey_integerTupleOfFinsupp
    (a : ℤ →₀ ℕ) (D : ℕ) (hcount : a.sum (fun _ k => k) = D) :
    integerTupleKey (integerTupleOfFinsupp a D hcount) = a := by
  classical
  let m := Finsupp.toMultiset a
  let hcard : Fintype.card m = D := by
    rw [Multiset.card_coe, Finsupp.card_toMultiset]
    simpa [Function.id_def] using hcount
  let e : Fin D ≃ m := (Fintype.equivFinOfCardEq hcard).symm
  have he : integerTupleOfFinsupp a D hcount = fun i => (e i : ℤ) := by
    rfl
  rw [he]
  ext r
  rw [integerTupleKey_count_map]
  have hmap : Multiset.map (fun i : Fin D => ((e i : m) : ℤ))
      (Finset.univ : Finset (Fin D)).val = m := by
    have heuniv := congrArg Finset.val (Finset.map_univ_equiv e)
    rw [Finset.map_val] at heuniv
    calc
      Multiset.map (fun i : Fin D => ((e i : m) : ℤ))
          (Finset.univ : Finset (Fin D)).val =
        Multiset.map (fun x : m => (x : ℤ))
          (Multiset.map e (Finset.univ : Finset (Fin D)).val) := by
            rw [Multiset.map_map]
            simp only [Function.comp_apply]
      _ = Multiset.map (fun x : m => (x : ℤ))
          (Finset.univ : Finset m).val := congrArg _ heuniv
      _ = m := Multiset.map_univ_coe m
  calc
    Multiset.count r
        (Multiset.map (fun i : Fin D => ((e i : m) : ℤ))
          (Finset.univ : Finset (Fin D)).val) =
        Multiset.count r m := congrArg _ hmap
    _ = a r := Finsupp.count_toMultiset a r

/-- The canonical tuple encoding is injective on multiplicity patterns of fixed total count. -/
theorem integerTupleOfFinsupp_injective (D : ℕ) :
    Function.Injective (fun a : {a : ℤ →₀ ℕ // a.sum (fun _ k => k) = D} =>
      integerTupleOfFinsupp a.1 D a.2) := by
  intro a b hab
  apply Subtype.ext
  rw [← integerTupleKey_integerTupleOfFinsupp a.1 D a.2,
    ← integerTupleKey_integerTupleOfFinsupp b.1 D b.2, hab]

theorem integerTupleKey_source {D : ℕ} (z : Fin D → ℤ) :
    gaussianOffsetSource (integerTupleKey z) = ∑ i, z i := by
  rw [gaussianOffsetSource, integerTupleKey,
    ← Finsupp.sum_finsetSum_index (s := Finset.univ)
      (g := fun i : Fin D => Finsupp.single (z i) 1)
      (h := fun r k => r * (k : ℤ))]
  · apply Finset.sum_congr rfl
    intro i _hi
    simp
  · intro r
    simp
  · intro r x y
    push_cast
    ring

theorem integerTupleKey_energy {D : ℕ} (z : Fin D → ℤ) :
    gaussianOffsetPatternEnergy (integerTupleKey z) = ∑ i, (z i) ^ 2 := by
  rw [gaussianOffsetPatternEnergy, integerTupleKey,
    ← Finsupp.sum_finsetSum_index (s := Finset.univ)
      (g := fun i : Fin D => Finsupp.single (z i) 1)
      (h := fun r k => r ^ 2 * (k : ℤ))]
  · apply Finset.sum_congr rfl
    intro i _hi
    simp
  · intro r
    simp
  · intro r x y
    push_cast
    ring

theorem integerTupleKey_totalCount {D : ℕ} (z : Fin D → ℤ) :
    (integerTupleKey z).sum (fun _ k => k) = D := by
  rw [integerTupleKey,
    ← Finsupp.sum_finsetSum_index (s := Finset.univ)
      (g := fun i : Fin D => Finsupp.single (z i) 1)
      (h := fun _ k => k)]
  · simp
  · intro r
    simp
  · intro r x y
    simp

theorem integerTupleOfFinsupp_source
    (a : ℤ →₀ ℕ) (D : ℕ) (hcount : a.sum (fun _ k => k) = D) :
    ∑ i, integerTupleOfFinsupp a D hcount i = gaussianOffsetSource a := by
  rw [← integerTupleKey_source (integerTupleOfFinsupp a D hcount),
    integerTupleKey_integerTupleOfFinsupp]

theorem integerTupleOfFinsupp_energy
    (a : ℤ →₀ ℕ) (D : ℕ) (hcount : a.sum (fun _ k => k) = D) :
    ∑ i, (integerTupleOfFinsupp a D hcount i) ^ 2 =
      gaussianOffsetPatternEnergy a := by
  rw [← integerTupleKey_energy (integerTupleOfFinsupp a D hcount),
    integerTupleKey_integerTupleOfFinsupp]

theorem gaussianOffsetEnergy_integerTupleOfFinsupp
    (a : ℤ →₀ ℕ) (D : ℕ) (hcount : a.sum (fun _ k => k) = D) :
    gaussianOffsetEnergy (integerTupleOfFinsupp a D hcount) =
      (gaussianOffsetPatternEnergy a : ℝ) := by
  rw [gaussianOffsetEnergy]
  exact_mod_cast integerTupleOfFinsupp_energy a D hcount

theorem integerLatticeMaxNatAbs_le_of_mem_box
    {ι : Type} [Fintype ι] {R : ℕ} {z : ι → ℤ}
    (hz : z ∈ integerLatticeBox ι R) :
    integerLatticeMaxNatAbs z ≤ R := by
  rw [integerLatticeMaxNatAbs]
  apply Finset.sup_le
  intro i _hi
  have hi := (mem_integerLatticeBox_iff ι R z).mp hz i
  have habs : |z i| ≤ (R : ℤ) := (abs_le).2 hi
  have hcast : ((z i).natAbs : ℤ) ≤ (R : ℤ) := by
    rw [Int.natCast_natAbs]
    exact habs
  exact_mod_cast hcast

theorem integerTupleOfFinsupp_support_subset_box
    (a : ℤ →₀ ℕ) (D : ℕ) (hcount : a.sum (fun _ k => k) = D) :
    a.support ⊆ gaussianOffsetInterval
      (integerLatticeMaxNatAbs (integerTupleOfFinsupp a D hcount)) := by
  classical
  let z := integerTupleOfFinsupp a D hcount
  have hkey : integerTupleKey z = a :=
    integerTupleKey_integerTupleOfFinsupp a D hcount
  intro r hr
  have hrKey : integerTupleKey z r ≠ 0 := by
    simpa only [hkey] using Finsupp.mem_support_iff.mp hr
  rw [integerTupleKey_count_map] at hrKey
  have hrmem : r ∈ Multiset.map z (Finset.univ : Finset (Fin D)).val :=
    Multiset.count_ne_zero.mp hrKey
  rw [Multiset.mem_map] at hrmem
  obtain ⟨i, _hi, hir⟩ := hrmem
  have habs : r.natAbs ≤ integerLatticeMaxNatAbs z := by
    rw [← hir]
    exact Finset.le_sup (f := fun i : Fin D => (z i).natAbs)
      (Finset.mem_univ i)
  simp only [gaussianOffsetInterval, Finset.mem_Icc, integerLatticeMaxNatAbs]
  have hcast : |r| ≤
      (integerLatticeMaxNatAbs z : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast habs
  exact (abs_le.mp hcast)

/-! ## Ambient Gaussian majorant -/

/-- The coordinatewise polynomial-Gaussian majorant supplied by
`summable_fintype_pi_polynomialGaussian`. -/
def gaussianCoordinateMajorant
    {ι : Type*} [Fintype ι] (J : ℕ) (B : ℝ) (z : ι → ℤ) : ℝ :=
  ∏ i, (1 + ((z i).natAbs : ℝ)) ^ J *
    Real.exp (-B * (z i : ℝ) ^ 2)

theorem gaussianCoordinateMajorant_nonneg
    {ι : Type*} [Fintype ι] (J : ℕ) (B : ℝ) (z : ι → ℤ) :
    0 ≤ gaussianCoordinateMajorant J B z := by
  unfold gaussianCoordinateMajorant
  positivity

/-- The maximum-coordinate polynomial weight is bounded by the product of the coordinatewise
weights.  Positivity of the dimension is essential only to choose a coordinate attaining the
finite maximum. -/
theorem one_add_latticeMax_pow_le_prod
    {ι : Type*} [Fintype ι] [Nonempty ι] (J : ℕ) (z : ι → ℤ) :
    (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J ≤
      ∏ i, (1 + ((z i).natAbs : ℝ)) ^ J := by
  classical
  obtain ⟨i, _hi, hiMax⟩ := Finset.exists_mem_eq_sup
    (s := (Finset.univ : Finset ι)) (f := fun i => (z i).natAbs)
    (Finset.univ_nonempty)
  have hfactor : (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J =
      (1 + ((z i).natAbs : ℝ)) ^ J := by
    simp only [integerLatticeMaxNatAbs]
    rw [hiMax]
  rw [hfactor]
  calc
    (1 + ((z i).natAbs : ℝ)) ^ J =
        ∏ j ∈ ({i} : Finset ι), (1 + ((z j).natAbs : ℝ)) ^ J := by simp
    _ ≤ ∏ j ∈ (Finset.univ : Finset ι),
        (1 + ((z j).natAbs : ℝ)) ^ J := by
      apply Finset.prod_le_prod_of_subset_of_one_le
      · exact Finset.singleton_subset_iff.mpr (Finset.mem_univ i)
      · intro j _hj
        positivity
      · intro j _hj _hne
        have hnat : (0 : ℝ) ≤ ((z j).natAbs : ℝ) := Nat.cast_nonneg _
        exact one_le_pow₀ (n := J) (by linarith)
    _ = ∏ j, (1 + ((z j).natAbs : ℝ)) ^ J := by rfl

/-- Exact product factorization of the coordinatewise Gaussian. -/
theorem prod_exp_neg_sq
    {ι : Type*} [Fintype ι] (B : ℝ) (z : ι → ℤ) :
    (∏ i, Real.exp (-B * (z i : ℝ) ^ 2)) =
      Real.exp (-B * gaussianOffsetEnergy z) := by
  rw [← Real.exp_sum]
  simp only [gaussianOffsetEnergy]
  congr 1
  rw [← Finset.mul_sum]

/-- A polynomial in the largest offset times the constrained Gaussian energy is bounded by a
constant multiple of the coordinatewise ambient Gaussian. -/
theorem maxPolynomial_gaussian_le_coordinateMajorant
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (J : ℕ) {B : ℝ} (_hB : 0 ≤ B) (Q₀ : ℝ) (z : ι → ℤ) :
    (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J *
        Real.exp (-B * (gaussianOffsetEnergy z - Q₀)) ≤
      Real.exp (B * Q₀) * gaussianCoordinateMajorant J B z := by
  have hpoly := one_add_latticeMax_pow_le_prod J z
  have hexp : Real.exp (-B * (gaussianOffsetEnergy z - Q₀)) =
      Real.exp (B * Q₀) *
        ∏ i, Real.exp (-B * (z i : ℝ) ^ 2) := by
    rw [prod_exp_neg_sq]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, gaussianCoordinateMajorant, Finset.prod_mul_distrib]
  have hnonneg : 0 ≤ Real.exp (B * Q₀) *
      ∏ i, Real.exp (-B * (z i : ℝ) ^ 2) := by positivity
  nlinarith

/-- Coordinatewise polynomial-Gaussian weights are summable on every finite integer lattice. -/
theorem summable_gaussianCoordinateMajorant
    (ι : Type) [Fintype ι] (J : ℕ) {B : ℝ} (hB : 0 < B) :
    Summable (gaussianCoordinateMajorant (ι := ι) J B) := by
  change Summable (fun z : ι → ℤ =>
    ∏ i, (1 + ((z i).natAbs : ℝ)) ^ J *
      Real.exp (-B * (z i : ℝ) ^ 2))
  exact summable_fintype_pi_polynomialGaussian
    ι (fun _ => J) (fun _ => B) (fun _ => hB)

/-- The max-polynomial Gaussian itself is summable, by comparison with the ambient product. -/
theorem summable_maxPolynomial_gaussian
    (ι : Type) [Fintype ι] [Nonempty ι]
    (J : ℕ) {B : ℝ} (hB : 0 < B) (Q₀ : ℝ) :
    Summable (fun z : ι → ℤ =>
      (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J *
        Real.exp (-B * (gaussianOffsetEnergy z - Q₀))) := by
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((summable_gaussianCoordinateMajorant ι J hB).mul_left (Real.exp (B * Q₀)))
  exact maxPolynomial_gaussian_le_coordinateMajorant J hB.le Q₀ z

/-- Every exterior Gaussian lattice tail is strictly positive.  This lets an independently
vanishing lower-degree/larger-source ADE residual be absorbed into the exterior tail at each fixed
window radius. -/
theorem gaussianExteriorTail_pos
    (ι : Type) [Fintype ι] [Nonempty ι]
    (J : ℕ) {B : ℝ} (hB : 0 < B) (Q₀ : ℝ) (R : ℕ) :
    0 < ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
      (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^ J *
        Real.exp (-B * (gaussianOffsetEnergy z.1 - Q₀)) := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  let z₀ : ι → ℤ := fun i => if i = i₀ then (R + 1 : ℕ) else 0
  have hz₀ : z₀ ∉ integerLatticeBox ι R := by
    intro hz
    have hi := (mem_integerLatticeBox_iff ι R z₀).mp hz i₀
    dsimp only [z₀] at hi
    simp only [ite_true] at hi
    omega
  let z : {z : ι → ℤ // z ∉ integerLatticeBox ι R} := ⟨z₀, hz₀⟩
  have hsum : Summable (fun z : {z : ι → ℤ // z ∉ integerLatticeBox ι R} =>
      (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^ J *
        Real.exp (-B * (gaussianOffsetEnergy z.1 - Q₀))) :=
    (summable_maxPolynomial_gaussian ι J hB Q₀).subtype _
  apply hsum.tsum_pos
  · intro y
    positivity
  · exact z
  · positivity

theorem tendsto_natAdd_pow_mul_exp_neg_mul_zero
    (K P : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℕ =>
      (((t + K : ℕ) : ℝ) ^ P) * Real.exp (-(c * (t : ℝ))))
      atTop (𝓝 0) := by
  have hcore := tendsto_natPow_mul_exp_neg_rpow_zero P hc one_pos
  have hmajor : Tendsto (fun t : ℕ =>
      (((2 : ℕ) ^ P : ℕ) : ℝ) *
        ((t : ℝ) ^ P * Real.exp (-(c * (t : ℝ))))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcore.const_mul ((((2 : ℕ) ^ P : ℕ) : ℝ))
  apply squeeze_zero'
  · exact Eventually.of_forall fun t => by positivity
  · filter_upwards [eventually_ge_atTop (max K 1)] with t ht
    have hKt : K ≤ t := (le_max_left K 1).trans ht
    have hbase : t + K ≤ 2 * t := by omega
    have hpow : (t + K) ^ P ≤ (2 * t) ^ P := Nat.pow_le_pow_left hbase P
    have hcast : (((t + K : ℕ) : ℝ) ^ P) ≤
        (((2 : ℕ) ^ P : ℕ) : ℝ) * (t : ℝ) ^ P := by
      exact_mod_cast (by simpa [mul_pow] using hpow)
    exact mul_le_mul_of_nonneg_right hcast (Real.exp_nonneg _)
  · exact hmajor

/-- The ambient product majorant outside growing integer boxes tends to zero. -/
theorem tendsto_gaussianCoordinateMajorant_tsum_outside_box_zero
    (ι : Type) [Fintype ι] (J : ℕ) (B : ℝ) :
    Tendsto (fun R =>
      ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
        gaussianCoordinateMajorant J B z.1)
      atTop (nhds 0) := by
  simpa [gaussianCoordinateMajorant] using
    (tendsto_polynomialGaussian_tsum_outside_box_zero
      ι (fun _ => J) (fun _ => B))

/-- The complete max-polynomial Gaussian face has vanishing mass outside growing finite boxes. -/
theorem tendsto_maxPolynomial_gaussian_tsum_outside_box_zero
    (ι : Type) [Fintype ι] [Nonempty ι]
    (J : ℕ) {B : ℝ} (hB : 0 < B) (Q₀ : ℝ) :
    Tendsto (fun R =>
      ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
        (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^ J *
          Real.exp (-B * (gaussianOffsetEnergy z.1 - Q₀)))
      atTop (nhds 0) := by
  let f : (ι → ℤ) → ℝ := fun z =>
    (1 + (integerLatticeMaxNatAbs z : ℝ)) ^ J *
      Real.exp (-B * (gaussianOffsetEnergy z - Q₀))
  have hsum : Summable f := summable_maxPolynomial_gaussian ι J hB Q₀
  exact (tendsto_tsum_compl_atTop_zero f).comp (integerLatticeBox_tendsto_atTop ι)


/-- The normalized aggregate of all lower-degree and larger-source atoms. -/
noncomputable def gaussianGapResidual
    (F : PowerSeries ℂ) (n D τ : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (B : ℝ) (S : ℤ)
    (H R₀ : ℕ) (a₀ : ℤ →₀ ℕ) (t : ℕ) : ℂ :=
  let q := t + R₀
  let m := atomValuation (fun i => B * (i : ℝ) ^ 2)
    (gaussianOffsetShiftedKey q a₀)
  ∑ ν ∈ gaussianGapActiveAtoms n D τ Q S q,
    (aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H) *
      (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ 2) ν - m)) : ℂ) *
        normalizedAtomPhase F (fun i => B * (i : ℝ) ^ 2) ν

/-- The lower-degree/larger-source normalized residual tends to zero as one aggregate. -/
theorem tendsto_gaussianGapResidual_zero
    {B : ℝ} (hB : 0 < B)
    {n D τ H : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} {S : ℤ} {R₀ : ℕ} {a₀ : ℤ →₀ ℕ}
    (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ 2)))
    (ha : anchor ∈ Q.support)
    (haD : jetMonomialDegree n anchor = D)
    (haMax : ∀ m ∈ Q.support,
      jetMonomialDegree n m = D →
        magnitudeShiftCode n Q m ≤ magnitudeShiftCode n Q anchor)
    (hDmax : D = magnitudeMaxJetDegree n Q) (hD : 0 < D)
    (hS : S + (magnitudeShiftCode n Q anchor : ℤ) =
      ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ))
    (ha₀ : a₀ ∈ gaussianOffsetFace D S R₀) :
    Tendsto (gaussianGapResidual F n D τ Q B S H R₀ a₀)
      atTop (𝓝 0) := by
  classical
  obtain ⟨c, hc, hgap⟩ := exists_eventually_gaussianGapActiveAtom_linear
    hB ha haD haMax hDmax hD hS ha₀
  obtain ⟨P, hmass⟩ := exists_aevalWeight_mass_natPow_bound n D τ Q
  have hmassShift := (tendsto_add_atTop_nat R₀).eventually hmass
  have hdecay := tendsto_natAdd_pow_mul_exp_neg_mul_zero R₀ P hc
  have hbound : ∀ᶠ t : ℕ in atTop,
      ‖gaussianGapResidual F n D τ Q B S H R₀ a₀ t‖ ≤
        (((t + R₀ : ℕ) : ℝ) ^ P) * Real.exp (-(c * (t : ℝ))) := by
    filter_upwards [hgap, hmassShift, eventually_ge_atTop 1] with
      t hgapT hmassT ht
    let q := t + R₀
    let T := gaussianGapActiveAtoms n D τ Q S q
    let den : ℂ := (q : ℂ) ^ H
    let m := atomValuation (fun i => B * (i : ℝ) ^ 2)
      (gaussianOffsetShiftedKey q a₀)
    have hden : 1 ≤ ‖den‖ := by
      dsimp only [den]
      rw [norm_pow, Complex.norm_natCast]
      exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ q by dsimp only [q]; omega))
    have hscaledMass :
        (∑ ν ∈ T, ‖aevalWeight n (D * q + τ) Q ν / den‖) ≤
          (q : ℝ) ^ P := by
      calc
        (∑ ν ∈ T, ‖aevalWeight n (D * q + τ) Q ν / den‖) ≤
            ∑ ν ∈ T, ‖aevalWeight n (D * q + τ) Q ν‖ := by
          apply Finset.sum_le_sum
          intro ν _hν
          rw [norm_div]
          exact div_le_self (norm_nonneg _) hden
        _ ≤ ∑ ν ∈ activeAevalAtoms n (D * q + τ) Q,
              ‖aevalWeight n (D * q + τ) Q ν‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => norm_nonneg _)
        _ ≤ (q : ℝ) ^ P := by simpa only [q] using hmassT
    change ‖∑ ν ∈ T,
      (aevalWeight n (D * q + τ) Q ν / den) *
        (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ 2) ν - m)) : ℂ) *
          normalizedAtomPhase F (fun i => B * (i : ℝ) ^ 2) ν‖ ≤ _
    calc
      ‖∑ ν ∈ T,
          (aevalWeight n (D * q + τ) Q ν / den) *
            (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ 2) ν - m)) : ℂ) *
              normalizedAtomPhase F (fun i => B * (i : ℝ) ^ 2) ν‖ ≤
          ∑ ν ∈ T,
            ‖(aevalWeight n (D * q + τ) Q ν / den) *
              (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ 2) ν - m)) : ℂ) *
                normalizedAtomPhase F (fun i => B * (i : ℝ) ^ 2) ν‖ :=
        norm_sum_le _ _
      _ ≤ ∑ ν ∈ T,
          ‖aevalWeight n (D * q + τ) Q ν / den‖ *
            Real.exp (-(c * (t : ℝ))) := by
        apply Finset.sum_le_sum
        intro ν hν
        have hνGap := hgapT ν (by simpa only [T, q] using hν)
        have hexp :
            Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ 2) ν - m)) ≤
              Real.exp (-(c * (t : ℝ))) := by
          apply Real.exp_le_exp.mpr
          dsimp only [m] at hνGap ⊢
          linarith
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _),
          norm_normalizedAtomPhase F (fun i => B * (i : ℝ) ^ 2) hb, mul_one]
        exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = (∑ ν ∈ T,
          ‖aevalWeight n (D * q + τ) Q ν / den‖) *
            Real.exp (-(c * (t : ℝ))) := by
        rw [Finset.sum_mul]
      _ ≤ (q : ℝ) ^ P * Real.exp (-(c * (t : ℝ))) :=
        mul_le_mul_of_nonneg_right hscaledMass (Real.exp_nonneg _)
      _ = (((t + R₀ : ℕ) : ℝ) ^ P) * Real.exp (-(c * (t : ℝ))) := by
        rfl
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun t => norm_nonneg _
  · exact hbound
  · exact hdecay

/-- One fixed constant covering both the cancellation-safe bounded-offset estimate and the
polynomial-mass estimate for offsets comparable with the translation center. -/
noncomputable def gaussianADEExteriorConstant
    (n D : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (B Q₀ : ℝ) (P : ℕ) : ℝ :=
  (gaussianPatternWeightNormalizationConstant n D Q +
      ((((n + 1) ^ P : ℕ) : ℝ))) * Real.exp (B * |Q₀|)

theorem gaussianADEExteriorConstant_nonneg
    (n D : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {B : ℝ} (hB : 0 ≤ B) (Q₀ : ℝ) (P : ℕ) :
    0 ≤ gaussianADEExteriorConstant n D Q B Q₀ P := by
  unfold gaussianADEExteriorConstant
  positivity

/-- Pointwise least-source exterior estimate.  Small offsets use cancellation-safe interpolation;
offsets comparable with `q` use the total ADE mass and spend half the Gaussian exponent. -/
theorem norm_normalized_gaussianExteriorAtom_le
    {B : ℝ} (hB : 0 < B)
    {n D τ H P q R : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {S : ℤ} {Q₀ : ℝ}
    (hmass :
      (∑ μ ∈ activeAevalAtoms n (D * q + τ) Q,
        ‖aevalWeight n (D * q + τ) Q μ‖) ≤ (q : ℝ) ^ P)
    (huniform : ∀ (A : ℕ) (a : ℤ →₀ ℕ)
        (ha : a ∈ gaussianOffsetFace D S A),
      (polynomialPatternWeightPoly n D A τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount ha) A)).natDegree ≤ H)
    (hHJ : H ≤ magnitudeMaxJetOrder n Q) (hq : 1 ≤ q)
    {ν : ℕ →₀ ℕ}
    (hν : ν ∈ gaussianExteriorActiveAtoms n D τ Q S q R) :
    let a := gaussianOffsetPatternOfKey q ν
    let hcount : a.sum (fun _ k => k) = D := by
      rw [gaussianOffsetPatternOfKey_totalCount]
      exact (Finset.mem_filter.mp hν).2.1
    let z := integerTupleOfFinsupp a D hcount
    ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ *
        Real.exp (-B * ((gaussianOffsetPatternEnergy a : ℝ) - Q₀)) ≤
      gaussianADEExteriorConstant n D Q B Q₀ P *
        (1 + (integerLatticeMaxNatAbs z : ℝ)) ^
          (magnitudeMaxJetOrder n Q + P) *
        Real.exp (-(B / 2) * (gaussianOffsetEnergy z - Q₀)) := by
  classical
  dsimp only
  let a := gaussianOffsetPatternOfKey q ν
  have hνData := (Finset.mem_filter.mp hν).2
  have hcountν : ν.sum (fun _ k => k) = D := hνData.1
  have hsourceν : gaussianAtomSignedSource D q ν = S := hνData.2.1
  have hνActive : ν ∈ activeAevalAtoms n (D * q + τ) Q :=
    (Finset.mem_filter.mp hν).1
  have hcounta : a.sum (fun _ k => k) = D := by
    rw [gaussianOffsetPatternOfKey_totalCount]
    exact hcountν
  let z := integerTupleOfFinsupp a D hcounta
  let A := integerLatticeMaxNatAbs z
  have hsourcea : gaussianOffsetSource a = S := by
    dsimp only [a]
    have hcountZ : (ν.sum (fun _ k => k) : ℤ) = (D : ℤ) := by
      exact_mod_cast hcountν
    rw [gaussianOffsetSource_patternOfKey, hcountZ]
    simpa only [gaussianAtomSignedSource, mul_comm] using hsourceν
  have hsuppa : a.support ⊆ gaussianOffsetInterval A := by
    simpa only [A, z] using integerTupleOfFinsupp_support_subset_box a D hcounta
  have haA : a ∈ gaussianOffsetFace D S A := by
    apply mem_gaussianOffsetFace.mpr
    refine ⟨?_, hsuppa, hsourcea⟩
    calc
      (∑ r ∈ gaussianOffsetInterval A, a r) = a.sum (fun _ k => k) := by
        symm
        exact Finsupp.sum_of_support_subset a hsuppa
          (fun _ k => k) (fun _ _ => rfl)
      _ = D := hcounta
  have henergy : gaussianOffsetEnergy z =
      (gaussianOffsetPatternEnergy a : ℝ) := by
    simpa only [z] using gaussianOffsetEnergy_integerTupleOfFinsupp a D hcounta
  have henergyNonneg : 0 ≤ (gaussianOffsetPatternEnergy a : ℝ) := by
    exact_mod_cast gaussianOffsetPatternEnergy_nonneg a
  have hexp :
      Real.exp (-B * ((gaussianOffsetPatternEnergy a : ℝ) - Q₀)) ≤
        Real.exp (B * |Q₀|) *
          Real.exp (-(B / 2) * (gaussianOffsetEnergy z - Q₀)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [henergy]
    have hneg : -|Q₀| ≤ Q₀ := neg_abs_le Q₀
    have habs : 0 ≤ |Q₀| := abs_nonneg Q₀
    nlinarith
  have hden : 1 ≤ ‖(q : ℂ) ^ H‖ := by
    rw [norm_pow, Complex.norm_natCast]
    exact one_le_pow₀ (by exact_mod_cast hq)
  have hmassν : ‖aevalWeight n (D * q + τ) Q ν‖ ≤ (q : ℝ) ^ P := by
    calc
      ‖aevalWeight n (D * q + τ) Q ν‖ ≤
          ∑ μ ∈ activeAevalAtoms n (D * q + τ) Q,
            ‖aevalWeight n (D * q + τ) Q μ‖ := by
        exact Finset.single_le_sum (fun μ _ => norm_nonneg _)
          (by simpa using hνActive)
      _ ≤ (q : ℝ) ^ P := hmass
  have hdivMass :
      ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ ≤ (q : ℝ) ^ P := by
    rw [norm_div]
    exact (div_le_self (norm_nonneg _) hden).trans hmassν
  have hweight :
      ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ ≤
        (gaussianPatternWeightNormalizationConstant n D Q +
          ((((n + 1) ^ P : ℕ) : ℝ))) *
          (1 + (A : ℝ)) ^ (magnitudeMaxJetOrder n Q + P) := by
    by_cases hsmall : A + n + 1 ≤ q
    · let p := gaussianOffsetPatternWindow a
        (gaussianOffsetFace_totalCount haA) A
      have hkey : shiftedAtomPatternKey q A p = ν := by
        calc
          shiftedAtomPatternKey q A p = gaussianOffsetShiftedKey q a :=
            shiftedAtomPatternKey_gaussianOffsetPatternWindow_eq haA (by omega)
          _ = ν := gaussianOffsetShiftedKey_patternOfKey q ν
      have hweightEval :
          aevalWeight n (D * q + τ) Q ν =
            (polynomialPatternWeightPoly n D A τ Q p).eval (q : ℂ) := by
        rw [← hkey]
        exact aevalWeight_shiftedAtomPatternKey_eq_eval_poly
          n D A τ Q p (gaussianOffsetPatternWindow_count haA) (by omega)
      have hinterp := norm_eval_gaussianOffsetPatternWeight_div_pow_le
        Q haA (huniform A a haA) hHJ (by omega : A + 1 ≤ q)
      have hpow :
          (((A + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) ≤
            (1 + (A : ℝ)) ^ (magnitudeMaxJetOrder n Q + P) := by
        push_cast
        rw [add_comm (A : ℝ) 1]
        exact pow_le_pow_right₀ (by positivity) (Nat.le_add_right _ _)
      rw [hweightEval]
      calc
        ‖(polynomialPatternWeightPoly n D A τ Q p).eval (q : ℂ) /
            (q : ℂ) ^ H‖ ≤
            gaussianPatternWeightNormalizationConstant n D Q *
              (((A + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) := hinterp
        _ ≤ gaussianPatternWeightNormalizationConstant n D Q *
              (1 + (A : ℝ)) ^ (magnitudeMaxJetOrder n Q + P) :=
          mul_le_mul_of_nonneg_left hpow
            (gaussianPatternWeightNormalizationConstant_nonneg n D Q)
        _ ≤ (gaussianPatternWeightNormalizationConstant n D Q +
              ((((n + 1) ^ P : ℕ) : ℝ))) *
              (1 + (A : ℝ)) ^ (magnitudeMaxJetOrder n Q + P) := by
          gcongr
          positivity
    · have hqA : q ≤ A + n := by omega
      have hbase : A + n ≤ (n + 1) * (A + 1) := by
        nlinarith [Nat.zero_le (n * A)]
      have hqpow : q ^ P ≤ (n + 1) ^ P * (A + 1) ^ P := by
        calc
          q ^ P ≤ ((n + 1) * (A + 1)) ^ P :=
            Nat.pow_le_pow_left (hqA.trans hbase) P
          _ = (n + 1) ^ P * (A + 1) ^ P := by rw [mul_pow]
      have hpowExp :
          (((A + 1) ^ P : ℕ) : ℝ) ≤
            (1 + (A : ℝ)) ^ (magnitudeMaxJetOrder n Q + P) := by
        push_cast
        rw [add_comm (A : ℝ) 1]
        exact pow_le_pow_right₀ (by positivity) (Nat.le_add_left P _)
      calc
        ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ ≤
            (q : ℝ) ^ P := hdivMass
        _ ≤ ((((n + 1) ^ P : ℕ) : ℝ)) *
            (((A + 1) ^ P : ℕ) : ℝ) := by exact_mod_cast hqpow
        _ ≤ ((((n + 1) ^ P : ℕ) : ℝ)) *
            (1 + (A : ℝ)) ^ (magnitudeMaxJetOrder n Q + P) :=
          mul_le_mul_of_nonneg_left hpowExp (by positivity)
        _ ≤ (gaussianPatternWeightNormalizationConstant n D Q +
              ((((n + 1) ^ P : ℕ) : ℝ))) *
              (1 + (A : ℝ)) ^ (magnitudeMaxJetOrder n Q + P) := by
          gcongr
          exact gaussianPatternWeightNormalizationConstant_nonneg n D Q
  change ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ *
      Real.exp (-B * ((gaussianOffsetPatternEnergy a : ℝ) - Q₀)) ≤ _
  rw [henergy]
  calc
    ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ *
        Real.exp (-B * (gaussianOffsetEnergy z - Q₀)) ≤
      ((gaussianPatternWeightNormalizationConstant n D Q +
          ((((n + 1) ^ P : ℕ) : ℝ))) *
        (1 + (A : ℝ)) ^ (magnitudeMaxJetOrder n Q + P)) *
          (Real.exp (B * |Q₀|) *
            Real.exp (-(B / 2) * (gaussianOffsetEnergy z - Q₀))) :=
      mul_le_mul hweight hexp (Real.exp_nonneg _) (by positivity)
    _ = gaussianADEExteriorConstant n D Q B Q₀ P *
        (1 + (integerLatticeMaxNatAbs z : ℝ)) ^
          (magnitudeMaxJetOrder n Q + P) *
        Real.exp (-(B / 2) * (gaussianOffsetEnergy z - Q₀)) := by
      dsimp only [gaussianADEExteriorConstant, A]
      ring

theorem gaussianExteriorTuple_not_mem_box
    {n D τ q R : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ} {S : ℤ}
    (hRq : R ≤ q) {ν : ℕ →₀ ℕ}
    (hν : ν ∈ gaussianExteriorActiveAtoms n D τ Q S q R) :
    let a := gaussianOffsetPatternOfKey q ν
    let hcount : a.sum (fun _ k => k) = D := by
      rw [gaussianOffsetPatternOfKey_totalCount]
      exact (Finset.mem_filter.mp hν).2.1
    integerTupleOfFinsupp a D hcount ∉ integerLatticeBox (Fin D) R := by
  classical
  dsimp only
  let a := gaussianOffsetPatternOfKey q ν
  have hcountν : ν.sum (fun _ k => k) = D := (Finset.mem_filter.mp hν).2.1
  have hnotWindow : ¬gaussianAtomInWindow q R ν :=
    (Finset.mem_filter.mp hν).2.2.2
  have hcounta : a.sum (fun _ k => k) = D := by
    rw [gaussianOffsetPatternOfKey_totalCount]
    exact hcountν
  let z := integerTupleOfFinsupp a D hcounta
  intro hz
  have hmax : integerLatticeMaxNatAbs z ≤ R :=
    integerLatticeMaxNatAbs_le_of_mem_box hz
  have hsuppMax := integerTupleOfFinsupp_support_subset_box a D hcounta
  have hinterval : gaussianOffsetInterval (integerLatticeMaxNatAbs z) ⊆
      gaussianOffsetInterval R := by
    intro r hr
    simp only [gaussianOffsetInterval, Finset.mem_Icc] at hr ⊢
    constructor <;> omega
  have hsuppR : a.support ⊆ gaussianOffsetInterval R :=
    hsuppMax.trans hinterval
  exact hnotWindow
    (gaussianAtomInWindow_of_patternOfKey_support_subset hRq hsuppR)

/-- The complete least-source exterior contribution is bounded by the ambient tuple Gaussian
tail.  Canonical tuple encoding prevents multiplicity-pattern overcounting. -/
theorem sum_norm_normalized_gaussianExteriorActiveAtoms_le_tail
    {B : ℝ} (hB : 0 < B)
    {n D τ H P q R : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {S : ℤ} {Q₀ : ℝ}
    (hD : 0 < D)
    (hmass :
      (∑ μ ∈ activeAevalAtoms n (D * q + τ) Q,
        ‖aevalWeight n (D * q + τ) Q μ‖) ≤ (q : ℝ) ^ P)
    (huniform : ∀ (A : ℕ) (a : ℤ →₀ ℕ)
        (ha : a ∈ gaussianOffsetFace D S A),
      (polynomialPatternWeightPoly n D A τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount ha) A)).natDegree ≤ H)
    (hHJ : H ≤ magnitudeMaxJetOrder n Q) (hq : 1 ≤ q) (hRq : R ≤ q) :
    (∑ ν ∈ gaussianExteriorActiveAtoms n D τ Q S q R,
      ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ *
        Real.exp (-B *
          ((gaussianOffsetPatternEnergy (gaussianOffsetPatternOfKey q ν) : ℝ) - Q₀))) ≤
      gaussianADEExteriorConstant n D Q B Q₀ P *
        ∑' z : {z : Fin D → ℤ // z ∉ integerLatticeBox (Fin D) R},
          (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^
              (magnitudeMaxJetOrder n Q + P) *
            Real.exp (-(B / 2) * (gaussianOffsetEnergy z.1 - Q₀)) := by
  classical
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  let E := gaussianExteriorActiveAtoms n D τ Q S q R
  let encode : ↥E →
      {z : Fin D → ℤ // z ∉ integerLatticeBox (Fin D) R} := fun ν =>
    let a := gaussianOffsetPatternOfKey q ν.1
    let hcount : a.sum (fun _ k => k) = D := by
      rw [gaussianOffsetPatternOfKey_totalCount]
      exact (Finset.mem_filter.mp ν.2).2.1
    ⟨integerTupleOfFinsupp a D hcount,
      gaussianExteriorTuple_not_mem_box hRq ν.2⟩
  have hencode : Function.Injective encode := by
    intro ν μ hνμ
    apply Subtype.ext
    let aν := gaussianOffsetPatternOfKey q ν.1
    let aμ := gaussianOffsetPatternOfKey q μ.1
    have hcountν : aν.sum (fun _ k => k) = D := by
      rw [gaussianOffsetPatternOfKey_totalCount]
      exact (Finset.mem_filter.mp ν.2).2.1
    have hcountμ : aμ.sum (fun _ k => k) = D := by
      rw [gaussianOffsetPatternOfKey_totalCount]
      exact (Finset.mem_filter.mp μ.2).2.1
    have htuple : integerTupleOfFinsupp aν D hcountν =
        integerTupleOfFinsupp aμ D hcountμ := congrArg Subtype.val hνμ
    have ha : aν = aμ := by
      have hsub :
          (⟨aν, hcountν⟩ : {a : ℤ →₀ ℕ // a.sum (fun _ k => k) = D}) =
            ⟨aμ, hcountμ⟩ := integerTupleOfFinsupp_injective D htuple
      exact congrArg Subtype.val hsub
    calc
      ν.1 = gaussianOffsetShiftedKey q aν :=
        (gaussianOffsetShiftedKey_patternOfKey q ν.1).symm
      _ = gaussianOffsetShiftedKey q aμ := by rw [ha]
      _ = μ.1 := gaussianOffsetShiftedKey_patternOfKey q μ.1
  let g : {z : Fin D → ℤ // z ∉ integerLatticeBox (Fin D) R} → ℝ := fun z =>
    (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^
        (magnitudeMaxJetOrder n Q + P) *
      Real.exp (-(B / 2) * (gaussianOffsetEnergy z.1 - Q₀))
  have hgsum : Summable g := by
    exact (summable_maxPolynomial_gaussian (Fin D)
      (magnitudeMaxJetOrder n Q + P) (by linarith : 0 < B / 2) Q₀).subtype _
  have hfinite : (∑ ν : ↥E, g (encode ν)) ≤ ∑' z, g z := by
    calc
      (∑ ν : ↥E, g (encode ν)) =
          ∑ z ∈ (Finset.univ : Finset ↥E).image encode, g z := by
        rw [Finset.sum_image]
        intro x _hx y _hy hxy
        exact hencode hxy
      _ ≤ ∑' z, g z := hgsum.sum_le_tsum _ (fun z _hz => by
        dsimp only [g]
        positivity)
  have hpoint : ∀ ν : ↥E,
      ‖aevalWeight n (D * q + τ) Q ν.1 / (q : ℂ) ^ H‖ *
          Real.exp (-B *
            ((gaussianOffsetPatternEnergy
              (gaussianOffsetPatternOfKey q ν.1) : ℝ) - Q₀)) ≤
        gaussianADEExteriorConstant n D Q B Q₀ P * g (encode ν) := by
    intro ν
    simpa only [g, encode, E] using
      norm_normalized_gaussianExteriorAtom_le hB hmass huniform hHJ hq ν.2
  calc
    (∑ ν ∈ gaussianExteriorActiveAtoms n D τ Q S q R,
        ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ *
          Real.exp (-B *
            ((gaussianOffsetPatternEnergy (gaussianOffsetPatternOfKey q ν) : ℝ) - Q₀))) =
        ∑ ν : ↥E,
          ‖aevalWeight n (D * q + τ) Q ν.1 / (q : ℂ) ^ H‖ *
            Real.exp (-B *
              ((gaussianOffsetPatternEnergy
                (gaussianOffsetPatternOfKey q ν.1) : ℝ) - Q₀)) := by
      simpa only [E] using (Finset.sum_attach
        (gaussianExteriorActiveAtoms n D τ Q S q R)
        (fun ν => ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ *
          Real.exp (-B *
            ((gaussianOffsetPatternEnergy
              (gaussianOffsetPatternOfKey q ν) : ℝ) - Q₀)))).symm
    _ ≤ ∑ ν : ↥E, gaussianADEExteriorConstant n D Q B Q₀ P *
          g (encode ν) := Finset.sum_le_sum fun ν _hν => hpoint ν
    _ = gaussianADEExteriorConstant n D Q B Q₀ P *
          ∑ ν : ↥E, g (encode ν) := by rw [Finset.mul_sum]
    _ ≤ gaussianADEExteriorConstant n D Q B Q₀ P * ∑' z, g z :=
      mul_le_mul_of_nonneg_left hfinite
        (gaussianADEExteriorConstant_nonneg n D Q hB.le Q₀ P)
    _ = gaussianADEExteriorConstant n D Q B Q₀ P *
        ∑' z : {z : Fin D → ℤ // z ∉ integerLatticeBox (Fin D) R},
          (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^
              (magnitudeMaxJetOrder n Q + P) *
            Real.exp (-(B / 2) * (gaussianOffsetEnergy z.1 - Q₀)) := by
      rfl

/-- One scaled normalized term in the exact ADE coefficient identity. -/
noncomputable def gaussianNormalizedADETerm
    (F : PowerSeries ℂ) (n N H : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (B m : ℝ)
    (q : ℕ) (ν : ℕ →₀ ℕ) : ℂ :=
  (aevalWeight n N Q ν / (q : ℂ) ^ H) *
    (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ 2) ν - m)) : ℂ) *
      normalizedAtomPhase F (fun i => B * (i : ℝ) ^ 2) ν

/-- Normalized finite-window grouped weight on the least Gaussian source face. -/
noncomputable def gaussianFaceWeight
    (n D τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (B Q₀ : ℝ) (H K q : ℕ)
    (p : Fin (2 * K + 1) → Fin (D + 1)) : ℂ :=
  (polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) /
      (q : ℂ) ^ H *
    (Real.exp (-B * ((gaussianWindowPatternEnergy p : ℝ) - Q₀)) : ℂ)

/-- Limiting finite-window grouped weight. -/
noncomputable def gaussianFaceWeightLimit
    (n D τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (B Q₀ : ℝ) (H K : ℕ)
    (p : Fin (2 * K + 1) → Fin (D + 1)) : ℂ :=
  (polynomialPatternWeightPoly n D K τ Q p).coeff H *
    (Real.exp (-B * ((gaussianWindowPatternEnergy p : ℝ) - Q₀)) : ℂ)

theorem tendsto_gaussianFaceWeight
    {n D τ H K : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (B Q₀ : ℝ) (p : Fin (2 * K + 1) → Fin (D + 1))
    (hdegree : (polynomialPatternWeightPoly n D K τ Q p).natDegree ≤ H) :
    Tendsto (fun t => gaussianFaceWeight n D τ Q B Q₀ H K (t + K) p)
      atTop (𝓝 (gaussianFaceWeightLimit n D τ Q B Q₀ H K p)) := by
  let E : ℂ :=
    (Real.exp (-B * ((gaussianWindowPatternEnergy p : ℝ) - Q₀)) : ℂ)
  have hpoly := (tendsto_complexPolynomial_eval_nat_div_pow
    (polynomialPatternWeightPoly n D K τ Q p) hdegree).comp
      (tendsto_add_atTop_nat K)
  simpa only [gaussianFaceWeight, gaussianFaceWeightLimit, E] using
    hpoly.mul_const E

/-- A least-source finite-window term is exactly its term in the normalized ADE identity. -/
theorem gaussianFaceWeight_mul_phase_eq_normalizedADETerm
    {B : ℝ} {n D τ H K q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {S : ℤ} {Q₀ : ℝ}
    (F : PowerSeries ℂ) (u : ℕ → ℂ)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(B * (i : ℝ) ^ 2)) : ℝ) : ℂ) * u i)
    {p : Fin (2 * K + 1) → Fin (D + 1)}
    (hp : p ∈ gaussianPolynomialPatternFace D S K)
    (hlarge : K + n ≤ q) :
    gaussianFaceWeight n D τ Q B Q₀ H K q p *
        ∏ r : Fin (2 * K + 1),
          u (windowShift q K (r : ℕ)) ^ (p r : ℕ) =
      gaussianNormalizedADETerm F n (D * q + τ) H Q B
        (B * ((D : ℝ) * (q : ℝ) ^ 2 + 2 * (q : ℝ) * (S : ℝ) + Q₀))
        q (shiftedAtomPatternKey q K p) := by
  have hpdata := mem_gaussianPolynomialPatternFace.mp hp
  let a := gaussianOffsetPatternOfWindow K p
  have ha : a ∈ gaussianOffsetFace D S K :=
    gaussianOffsetPatternOfWindow_mem_face_centered p hpdata.1 hpdata.2
  have hpback : gaussianOffsetPatternWindow a
      (gaussianOffsetFace_totalCount ha) K = p :=
    gaussianOffsetPatternWindow_patternOfWindow_eq p hpdata.1 hpdata.2
  have hweight :
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) =
        (polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) :=
    aevalWeight_shiftedAtomPatternKey_eq_eval_poly
      n D K τ Q p hpdata.1 hlarge
  have hvaluation := atomValuation_gaussianOffsetShiftedKey B ha
    (by omega : K ≤ q)
  have hkey : shiftedAtomPatternKey q K p = gaussianOffsetShiftedKey q a :=
    shiftedAtomPatternKey_gaussianOffsetPatternOfWindow_eq p (by omega)
  have henergy : gaussianWindowPatternEnergy p = gaussianOffsetPatternEnergy a :=
    gaussianWindowPatternEnergy_eq_patternOfWindow p hpdata.1 hpdata.2
  rw [gaussianFaceWeight, gaussianNormalizedADETerm,
    normalizedAtomPhase_shiftedAtomPatternKey_eq F
      (fun i => B * (i : ℝ) ^ 2) u hcoeff, hweight]
  rw [hkey] at hvaluation
  rw [hvaluation, henergy]
  push_cast
  ring_nf
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  ring

/-- Summing the complete finite Gaussian pattern face is the same as summing its active
least-source interior atoms.  Inactive image keys disappear because their grouped ADE weight is
zero; no survivor or noncancellation hypothesis is imposed on the individual patterns. -/
theorem sum_gaussianFaceWeight_mul_phase_eq_interior
    {B : ℝ} {n D τ H K q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {S : ℤ} {Q₀ : ℝ}
    (F : PowerSeries ℂ) (u : ℕ → ℂ)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(B * (i : ℝ) ^ 2)) : ℝ) : ℂ) * u i)
    (hKq : K ≤ q) (hlarge : K + n ≤ q) :
    (∑ p ∈ gaussianPolynomialPatternFace D S K,
      gaussianFaceWeight n D τ Q B Q₀ H K q p *
        ∏ r : Fin (2 * K + 1),
          u (windowShift q K (r : ℕ)) ^ (p r : ℕ)) =
      ∑ ν ∈ gaussianInteriorActiveAtoms n D τ Q S q K,
        gaussianNormalizedADETerm F n (D * q + τ) H Q B
          (B * ((D : ℝ) * (q : ℝ) ^ 2 +
            2 * (q : ℝ) * (S : ℝ) + Q₀)) q ν := by
  classical
  let Face := gaussianPolynomialPatternFace D S K
  let Ckey := Face.image (shiftedAtomPatternKey q K)
  let f : (ℕ →₀ ℕ) → ℂ := fun ν =>
    gaussianNormalizedADETerm F n (D * q + τ) H Q B
      (B * ((D : ℝ) * (q : ℝ) ^ 2 +
        2 * (q : ℝ) * (S : ℝ) + Q₀)) q ν
  calc
    (∑ p ∈ gaussianPolynomialPatternFace D S K,
        gaussianFaceWeight n D τ Q B Q₀ H K q p *
          ∏ r : Fin (2 * K + 1),
            u (windowShift q K (r : ℕ)) ^ (p r : ℕ)) =
        ∑ p ∈ Face, f (shiftedAtomPatternKey q K p) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact gaussianFaceWeight_mul_phase_eq_normalizedADETerm
        F u hcoeff (by simpa only [Face] using hp) hlarge
    _ = ∑ ν ∈ Ckey, f ν := by
      simpa only [Ckey] using (sum_image_shiftedAtomPatternKey Face f).symm
    _ = ∑ ν ∈ Ckey.filter
          (fun ν => ν ∈ activeAevalAtoms n (D * q + τ) Q), f ν := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro ν hνC hνNot
      have hnotActive : ν ∉ activeAevalAtoms n (D * q + τ) Q := by
        intro hactive
        exact hνNot (Finset.mem_filter.mpr ⟨hνC, hactive⟩)
      have hwzero := aevalWeight_eq_zero_of_not_mem_activeAevalAtoms hnotActive
      dsimp only [f, gaussianNormalizedADETerm]
      simp only [hwzero, zero_div, zero_mul]
    _ = ∑ ν ∈ gaussianInteriorActiveAtoms n D τ Q S q K, f ν := by
      rw [gaussianInteriorActiveAtoms_eq_filter_image_face hKq]
      rfl
    _ = ∑ ν ∈ gaussianInteriorActiveAtoms n D τ Q S q K,
        gaussianNormalizedADETerm F n (D * q + τ) H Q B
          (B * ((D : ℝ) * (q : ℝ) ^ 2 +
            2 * (q : ℝ) * (S : ℝ) + Q₀)) q ν := by
      rfl

/-! ## Exact normalized face/remainder splitting -/

/-- On a degree-`D`, signed-source-`S` atom, the normalized ADE term has exactly the intrinsic
Gaussian offset energy. -/
theorem norm_gaussianNormalizedADETerm_of_leastSource
    {B : ℝ} {n D τ H q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {S : ℤ} {Q₀ : ℝ}
    (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ 2)))
    {ν : ℕ →₀ ℕ} (hcount : ν.sum (fun _ k => k) = D)
    (hsource : gaussianAtomSignedSource D q ν = S) :
    ‖gaussianNormalizedADETerm F n (D * q + τ) H Q B
        (B * ((D : ℝ) * (q : ℝ) ^ 2 +
          2 * (q : ℝ) * (S : ℝ) + Q₀)) q ν‖ =
      ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ *
        Real.exp (-B *
          ((gaussianOffsetPatternEnergy
            (gaussianOffsetPatternOfKey q ν) : ℝ) - Q₀)) := by
  have hsourcePattern :
      gaussianOffsetSource (gaussianOffsetPatternOfKey q ν) = S := by
    have hcountZ : (ν.sum (fun _ k => k) : ℤ) = (D : ℤ) := by
      exact_mod_cast hcount
    rw [gaussianOffsetSource_patternOfKey, hcountZ]
    simpa only [gaussianAtomSignedSource, mul_comm] using hsource
  have hvaluation := atomValuation_gaussianOffsetPatternOfKey B hcount hsourcePattern
  rw [gaussianNormalizedADETerm, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_normalizedAtomPhase F (fun i => B * (i : ℝ) ^ 2) hb, mul_one,
    hvaluation]
  congr 2
  ring

/-- Abstract exact-identity splitter.  A selected finite subface of a finite zero sum is bounded
by the norm mass of its complementary remainder. -/
theorem norm_subface_sum_le_remainder_of_sum_eq_zero
    {α : Type*} [DecidableEq α] (T C : Finset α) (hCT : C ⊆ T)
    (f : α → ℂ) (hzero : ∑ x ∈ T, f x = 0) :
    ‖∑ x ∈ C, f x‖ ≤ ∑ x ∈ T \ C, ‖f x‖ := by
  have hbalance : ∑ x ∈ C, f x = -∑ x ∈ T \ C, f x :=
    normalized_cluster_balance_of_identity T C hCT f hzero
  rw [hbalance, norm_neg]
  exact norm_sum_le _ _

/-- Cancellation-preserving exact-identity splitter.  The gap aggregate remains inside one norm;
only the genuinely exterior class is replaced by its norm mass. -/
theorem norm_subface_sum_le_norm_gap_add_exterior_of_sum_eq_zero
    {α : Type*} [DecidableEq α]
    (T C G E : Finset α) (hCT : C ⊆ T)
    (hrem : T \ C = G ∪ E) (hGE : Disjoint G E)
    (f : α → ℂ) (hzero : ∑ x ∈ T, f x = 0) :
    ‖∑ x ∈ C, f x‖ ≤
      ‖∑ x ∈ G, f x‖ + ∑ x ∈ E, ‖f x‖ := by
  have hbalance := normalized_cluster_balance_of_identity T C hCT f hzero
  rw [hbalance, norm_neg, hrem, Finset.sum_union hGE]
  exact (norm_add_le _ _).trans
    (add_le_add_left (norm_sum_le _ _) _)

/-- The exact normalized ADE coefficient identity written directly in terms of
`gaussianNormalizedADETerm`. -/
theorem sum_gaussianNormalizedADETerm_active_eq_zero
    {B m : ℝ} {n N H q : ℕ}
    (F : PowerSeries ℂ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hrel : aeval (formalJets n F) Q = 0) :
    ∑ ν ∈ activeAevalAtoms n N Q,
      gaussianNormalizedADETerm F n N H Q B m q ν = 0 := by
  let fraw : (ℕ →₀ ℕ) → ℂ := fun ν =>
    aevalWeight n N Q ν *
      (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ 2) ν - m)) : ℂ) *
        normalizedAtomPhase F (fun i => B * (i : ℝ) ^ 2) ν
  have hzeroRaw : ∑ ν ∈ activeAevalAtoms n N Q, fraw ν = 0 := by
    simpa only [fraw] using normalized_active_aeval_coefficient_identity
      n N F Q (fun i => B * (i : ℝ) ^ 2) hrel m
  calc
    (∑ ν ∈ activeAevalAtoms n N Q,
        gaussianNormalizedADETerm F n N H Q B m q ν) =
        (∑ ν ∈ activeAevalAtoms n N Q, fraw ν) / (q : ℂ) ^ H := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ν _hν
      dsimp only [gaussianNormalizedADETerm, fraw]
      ring
    _ = 0 := by rw [hzeroRaw, zero_div]

/-- Exact four-way Gaussian ADE estimate.  Lower-degree and larger-source atoms remain one
cancellation-sensitive gap aggregate; only the exterior least-source class is estimated termwise. -/
theorem norm_sum_gaussianInteriorActiveAtoms_le_gap_add_exterior
    {B m : ℝ} {n D τ H q R : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} {S : ℤ}
    (F : PowerSeries ℂ)
    (hrel : aeval (formalJets n F) Q = 0)
    (ha : anchor ∈ Q.support)
    (haD : jetMonomialDegree n anchor = D)
    (haMax : ∀ a ∈ Q.support,
      jetMonomialDegree n a = D →
        magnitudeShiftCode n Q a ≤ magnitudeShiftCode n Q anchor)
    (hDmax : D = magnitudeMaxJetDegree n Q)
    (hS : S + (magnitudeShiftCode n Q anchor : ℤ) =
      ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ)) :
    ‖∑ ν ∈ gaussianInteriorActiveAtoms n D τ Q S q R,
        gaussianNormalizedADETerm F n (D * q + τ) H Q B m q ν‖ ≤
      ‖∑ ν ∈ gaussianGapActiveAtoms n D τ Q S q,
        gaussianNormalizedADETerm F n (D * q + τ) H Q B m q ν‖ +
      ∑ ν ∈ gaussianExteriorActiveAtoms n D τ Q S q R,
        ‖gaussianNormalizedADETerm F n (D * q + τ) H Q B m q ν‖ := by
  classical
  let T := activeAevalAtoms n (D * q + τ) Q
  let I := gaussianInteriorActiveAtoms n D τ Q S q R
  let G := gaussianGapActiveAtoms n D τ Q S q
  let E := gaussianExteriorActiveAtoms n D τ Q S q R
  let f : (ℕ →₀ ℕ) → ℂ := fun ν =>
    gaussianNormalizedADETerm F n (D * q + τ) H Q B m q ν
  have hIT : I ⊆ T := by
    intro ν hν
    exact (Finset.mem_filter.mp hν).1
  have hrem : T \ I = G ∪ E := by
    simpa only [T, I, G, E] using
      activeAevalAtoms_sdiff_gaussianInterior_eq_gap_union_exterior
        ha haD haMax hDmax hS
  have hGE : Disjoint G E := by
    simpa only [G, E] using
      (gaussianGapActiveAtoms_disjoint_gaussianExteriorActiveAtoms
        (n := n) (D := D) (τ := τ) (q := q) (R := R) (Q := Q) (S := S))
  have hzero : ∑ ν ∈ T, f ν = 0 := by
    simpa only [T, f] using
      sum_gaussianNormalizedADETerm_active_eq_zero
        (B := B) (m := m) (H := H) (q := q) F Q hrel
  simpa only [I, G, E, f] using
    norm_subface_sum_le_norm_gap_add_exterior_of_sum_eq_zero
      T I G E hIT hrem hGE f hzero

/-- Every enlarged finite Gaussian face is eventually bounded by one fixed-constant ambient
lattice tail.  The enlarged face radius is `R + R₀`, so it always contains the stable atom; the
right-hand tail still starts outside the requested compiler radius `R`. -/
theorem exists_eventually_norm_gaussianFaceCluster_le_tail
    {B : ℝ} (hB : 0 < B)
    {F : PowerSeries ℂ} {u : ℕ → ℂ}
    {n D τ H : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} {S : ℤ}
    {R₀ : ℕ} {a₀ : ℤ →₀ ℕ}
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(B * (i : ℝ) ^ 2)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ i, ‖u i‖ = 1)
    (hrel : aeval (formalJets n F) Q = 0)
    (ha : anchor ∈ Q.support)
    (haD : jetMonomialDegree n anchor = D)
    (haMax : ∀ m ∈ Q.support,
      jetMonomialDegree n m = D →
        magnitudeShiftCode n Q m ≤ magnitudeShiftCode n Q anchor)
    (hDmax : D = magnitudeMaxJetDegree n Q) (hD : 0 < D)
    (hS : S + (magnitudeShiftCode n Q anchor : ℤ) =
      ((τ + magnitudeMaxJetOrder n Q : ℕ) : ℤ))
    (ha₀ : a₀ ∈ gaussianOffsetFace D S R₀)
    (hHJ : H ≤ magnitudeMaxJetOrder n Q)
    (huniform : ∀ (A : ℕ) (a : ℤ →₀ ℕ)
        (haA : a ∈ gaussianOffsetFace D S A),
      (polynomialPatternWeightPoly n D A τ Q
        (gaussianOffsetPatternWindow a
          (gaussianOffsetFace_totalCount haA) A)).natDegree ≤ H) :
    ∃ P : ℕ, ∀ R : ℕ, ∀ᶠ t : ℕ in atTop,
      ‖∑ p ∈ gaussianPolynomialPatternFace D S (R + R₀),
        gaussianFaceWeight n D τ Q B
            (gaussianOffsetPatternEnergy a₀ : ℝ) H (R + R₀)
            (t + (R + R₀)) p *
          ∏ r : Fin (2 * (R + R₀) + 1),
            u (t + (r : ℕ)) ^ (p r : ℕ)‖ ≤
        (gaussianADEExteriorConstant n D Q B
            (gaussianOffsetPatternEnergy a₀ : ℝ) P + 1) *
          ∑' z : {z : Fin D → ℤ // z ∉ integerLatticeBox (Fin D) R},
            (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^
                (magnitudeMaxJetOrder n Q + P) *
              Real.exp (-(B / 2) *
                (gaussianOffsetEnergy z.1 -
                  (gaussianOffsetPatternEnergy a₀ : ℝ))) := by
  classical
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  have hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ 2)) := by
    intro i
    rw [hcoeff, norm_mul, huNorm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  obtain ⟨P, hmass⟩ := exists_aevalWeight_mass_natPow_bound n D τ Q
  refine ⟨P, ?_⟩
  intro R
  let K := R + R₀
  let Q₀ : ℝ := gaussianOffsetPatternEnergy a₀
  let J := magnitudeMaxJetOrder n Q + P
  let C := gaussianADEExteriorConstant n D Q B Q₀ P
  let Tail : ℝ :=
    ∑' z : {z : Fin D → ℤ // z ∉ integerLatticeBox (Fin D) R},
      (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^ J *
        Real.exp (-(B / 2) * (gaussianOffsetEnergy z.1 - Q₀))
  have hTail : 0 < Tail := by
    simpa only [Tail, J] using
      gaussianExteriorTail_pos (Fin D) J (by linarith : 0 < B / 2) Q₀ R
  have hgap := tendsto_gaussianGapResidual_zero (H := H) hB F hb
    ha haD haMax hDmax hD hS ha₀
  have hgapShift : Tendsto (fun t : ℕ =>
      ‖gaussianGapResidual F n D τ Q B S H R₀ a₀ (t + R)‖)
      atTop (𝓝 0) := by
    simpa only [norm_zero] using hgap.norm.comp (tendsto_add_atTop_nat R)
  have hgapSmall : ∀ᶠ t : ℕ in atTop,
      ‖gaussianGapResidual F n D τ Q B S H R₀ a₀ (t + R)‖ ≤ Tail :=
    (hgapShift.eventually_lt_const hTail).mono fun _ ht => ht.le
  have hmassShift := (tendsto_add_atTop_nat K).eventually hmass
  filter_upwards [hgapSmall, hmassShift,
    eventually_ge_atTop (max n 1)] with t hgapT hmassT ht
  let q := t + K
  have hKq : K ≤ q := by dsimp only [q]; omega
  have hlarge : K + n ≤ q := by
    have hn : n ≤ t := (le_max_left n 1).trans ht
    dsimp only [q]
    omega
  have hq : 1 ≤ q := by
    have ht1 : 1 ≤ t := (le_max_right n 1).trans ht
    dsimp only [q]
    omega
  have hRq : R ≤ q := by dsimp only [q, K]; omega
  have hfaceEq := sum_gaussianFaceWeight_mul_phase_eq_interior
    (n := n) (D := D) (τ := τ) (H := H) (K := K) (q := q)
    (Q := Q) (S := S) (Q₀ := Q₀) F u hcoeff hKq hlarge
  have hsplit := norm_sum_gaussianInteriorActiveAtoms_le_gap_add_exterior
    (B := B) (m := B * ((D : ℝ) * (q : ℝ) ^ 2 +
      2 * (q : ℝ) * (S : ℝ) + Q₀))
    (H := H) (q := q) (R := K) F hrel ha haD haMax hDmax hS
  have hgapEq :
      (∑ ν ∈ gaussianGapActiveAtoms n D τ Q S q,
        gaussianNormalizedADETerm F n (D * q + τ) H Q B
          (B * ((D : ℝ) * (q : ℝ) ^ 2 +
            2 * (q : ℝ) * (S : ℝ) + Q₀)) q ν) =
        gaussianGapResidual F n D τ Q B S H R₀ a₀ (t + R) := by
    have hbase := atomValuation_gaussianOffsetShiftedKey B ha₀
      (by dsimp only [q, K]; omega : R₀ ≤ q)
    simp only [gaussianGapResidual, gaussianNormalizedADETerm]
    simp only [q, K, add_assoc]
    rw [hbase]
    rfl
  have hnormExterior :
      (∑ ν ∈ gaussianExteriorActiveAtoms n D τ Q S q K,
          ‖gaussianNormalizedADETerm F n (D * q + τ) H Q B
            (B * ((D : ℝ) * (q : ℝ) ^ 2 +
              2 * (q : ℝ) * (S : ℝ) + Q₀)) q ν‖) =
        ∑ ν ∈ gaussianExteriorActiveAtoms n D τ Q S q K,
          ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ *
            Real.exp (-B *
              ((gaussianOffsetPatternEnergy
                (gaussianOffsetPatternOfKey q ν) : ℝ) - Q₀)) := by
    apply Finset.sum_congr rfl
    intro ν hν
    have hνData := (Finset.mem_filter.mp hν).2
    exact norm_gaussianNormalizedADETerm_of_leastSource
      F hb hνData.1 hνData.2.1
  have hsubset := gaussianExteriorActiveAtoms_subset_of_radius_le
    (n := n) (D := D) (τ := τ) (q := q) (Q := Q) (S := S)
    (show R ≤ K by dsimp only [K]; omega)
  have hsmallExterior :
      (∑ ν ∈ gaussianExteriorActiveAtoms n D τ Q S q K,
        ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ *
          Real.exp (-B *
            ((gaussianOffsetPatternEnergy
              (gaussianOffsetPatternOfKey q ν) : ℝ) - Q₀))) ≤
        ∑ ν ∈ gaussianExteriorActiveAtoms n D τ Q S q R,
        ‖aevalWeight n (D * q + τ) Q ν / (q : ℂ) ^ H‖ *
          Real.exp (-B *
            ((gaussianOffsetPatternEnergy
              (gaussianOffsetPatternOfKey q ν) : ℝ) - Q₀)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => by positivity)
  have htail := sum_norm_normalized_gaussianExteriorActiveAtoms_le_tail
    (n := n) (D := D) (τ := τ) (H := H) (P := P) (q := q) (R := R)
    (Q := Q) (S := S) (Q₀ := Q₀)
    hB hD hmassT huniform hHJ hq hRq
  have hexterior :
      (∑ ν ∈ gaussianExteriorActiveAtoms n D τ Q S q K,
        ‖gaussianNormalizedADETerm F n (D * q + τ) H Q B
          (B * ((D : ℝ) * (q : ℝ) ^ 2 +
            2 * (q : ℝ) * (S : ℝ) + Q₀)) q ν‖) ≤ C * Tail := by
    rw [hnormExterior]
    exact hsmallExterior.trans (by simpa only [C, Tail, J] using htail)
  have hfaceEq' :
      (∑ p ∈ gaussianPolynomialPatternFace D S K,
        gaussianFaceWeight n D τ Q B Q₀ H K q p *
          ∏ r : Fin (2 * K + 1), u (t + (r : ℕ)) ^ (p r : ℕ)) =
        ∑ ν ∈ gaussianInteriorActiveAtoms n D τ Q S q K,
          gaussianNormalizedADETerm F n (D * q + τ) H Q B
            (B * ((D : ℝ) * (q : ℝ) ^ 2 +
              2 * (q : ℝ) * (S : ℝ) + Q₀)) q ν := by
    simpa [q, windowShift] using hfaceEq
  rw [show
    (∑ p ∈ gaussianPolynomialPatternFace D S (R + R₀),
      gaussianFaceWeight n D τ Q B
          (gaussianOffsetPatternEnergy a₀ : ℝ) H (R + R₀)
          (t + (R + R₀)) p *
        ∏ r : Fin (2 * (R + R₀) + 1),
          u (t + (r : ℕ)) ^ (p r : ℕ)) =
      ∑ ν ∈ gaussianInteriorActiveAtoms n D τ Q S q K,
        gaussianNormalizedADETerm F n (D * q + τ) H Q B
          (B * ((D : ℝ) * (q : ℝ) ^ 2 +
            2 * (q : ℝ) * (S : ℝ) + Q₀)) q ν by
      simpa only [K, Q₀, q] using hfaceEq']
  calc
    ‖∑ ν ∈ gaussianInteriorActiveAtoms n D τ Q S q K,
        gaussianNormalizedADETerm F n (D * q + τ) H Q B
          (B * ((D : ℝ) * (q : ℝ) ^ 2 +
            2 * (q : ℝ) * (S : ℝ) + Q₀)) q ν‖
        ≤ ‖gaussianGapResidual F n D τ Q B S H R₀ a₀ (t + R)‖ +
            ∑ ν ∈ gaussianExteriorActiveAtoms n D τ Q S q K,
              ‖gaussianNormalizedADETerm F n (D * q + τ) H Q B
                (B * ((D : ℝ) * (q : ℝ) ^ 2 +
                  2 * (q : ℝ) * (S : ℝ) + Q₀)) q ν‖ := by
          simpa only [hgapEq] using hsplit
    _ ≤ Tail + C * Tail := add_le_add hgapT hexterior
    _ = (C + 1) * Tail := by ring
    _ = (gaussianADEExteriorConstant n D Q B
          (gaussianOffsetPatternEnergy a₀ : ℝ) P + 1) *
        ∑' z : {z : Fin D → ℤ // z ∉ integerLatticeBox (Fin D) R},
          (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^
              (magnitudeMaxJetOrder n Q + P) *
            Real.exp (-(B / 2) *
              (gaussianOffsetEnergy z.1 -
                (gaussianOffsetPatternEnergy a₀ : ℝ))) := by
      rfl

/-- Concrete normalized-ADE splitter.  It applies the exact coefficient identity, divides by one
common polynomial normalization, and uses the unit norm of every normalized atom phase. -/
theorem norm_normalized_active_aeval_subface_le_remainder
    {n N : ℕ} (F : PowerSeries ℂ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (b : ℕ → ℝ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (hrel : aeval (formalJets n F) Q = 0)
    (C : Finset (ℕ →₀ ℕ))
    (hC : C ⊆ activeAevalAtoms n N Q) (m : ℝ) (den : ℂ) :
    ‖∑ ν ∈ C,
        (aevalWeight n N Q ν / den) *
          (Real.exp (-(atomValuation b ν - m)) : ℂ) *
            normalizedAtomPhase F b ν‖ ≤
      ∑ ν ∈ activeAevalAtoms n N Q \ C,
        ‖aevalWeight n N Q ν / den‖ *
          Real.exp (-(atomValuation b ν - m)) := by
  classical
  let T := activeAevalAtoms n N Q
  let fraw : (ℕ →₀ ℕ) → ℂ := fun ν =>
    aevalWeight n N Q ν *
      (Real.exp (-(atomValuation b ν - m)) : ℂ) *
        normalizedAtomPhase F b ν
  let fscaled : (ℕ →₀ ℕ) → ℂ := fun ν =>
    (aevalWeight n N Q ν / den) *
      (Real.exp (-(atomValuation b ν - m)) : ℂ) *
        normalizedAtomPhase F b ν
  have hzeroRaw : ∑ ν ∈ T, fraw ν = 0 := by
    simpa only [T, fraw] using
      normalized_active_aeval_coefficient_identity n N F Q b hrel m
  have hzero : ∑ ν ∈ T, fscaled ν = 0 := by
    calc
      ∑ ν ∈ T, fscaled ν = (∑ ν ∈ T, fraw ν) / den := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ν _hν
        dsimp only [fscaled, fraw]
        ring
      _ = 0 := by rw [hzeroRaw, zero_div]
  have hsplit := norm_subface_sum_le_remainder_of_sum_eq_zero
    T C hC fscaled hzero
  simpa only [T, fscaled, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_normalizedAtomPhase F b hb, mul_one] using hsplit

/-! ## Approximate finite Fourier inversion -/

/-- Approximate torsion Fourier inversion: if a finite multiplicity face is uniformly bounded by
`epsilon` on the full `(D+1)`-torsion state space, then each individual Fourier coefficient has
norm at most `epsilon`.  This is the quantitative replacement for
`face_fin_weights_eq_zero` needed before sending a Gaussian window radius to infinity. -/
theorem norm_face_fin_weight_le_of_uniform_torsion_bound
    {M D : ℕ} (F : Finset (Fin M → Fin (D + 1)))
    (ell : (Fin M → Fin (D + 1)) → ℂ) {epsilon : ℝ} (_hepsilon : 0 ≤ epsilon)
    (hbound : ∀ s : Fin M → ℂ, (∀ r, s r ^ (D + 1) = 1) →
      ‖∑ p ∈ F, ell p * ∏ r, s r ^ (p r : ℕ)‖ ≤ epsilon) :
    ∀ p ∈ F, ‖ell p‖ ≤ epsilon := by
  classical
  intro p₀ hp₀
  let m := D + 1
  have hm0 : m ≠ 0 := by omega
  set zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hzetaDef
  have hzeta : IsPrimitiveRoot zeta m := Complex.isPrimitiveRoot_exp m hm0
  have hzeta0 : zeta ≠ 0 := hzeta.ne_zero hm0
  let states : Finset (Fin M → ℕ) :=
    Fintype.piFinset (fun _ : Fin M => Finset.range m)
  let faceValue : (Fin M → ℕ) → ℂ := fun x =>
    ∑ p ∈ F, ell p * ∏ i, zeta ^ ((p i : ℤ) * (x i : ℤ))
  have hstateBound : ∀ x ∈ states, ‖faceValue x‖ ≤ epsilon := by
    intro x hx
    have hxmem : ∀ i, x i ∈ Finset.range m := by
      simpa [states, Fintype.mem_piFinset] using hx
    let s : Fin M → ℂ := fun i => zeta ^ x i
    have hs : ∀ i, s i ^ (D + 1) = 1 := by
      intro i
      dsimp [s, m]
      rw [← pow_mul, mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]
    have hb := hbound s hs
    have heq : faceValue x =
        ∑ p ∈ F, ell p * ∏ i, s i ^ (p i : ℕ) := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      dsimp [s]
      rw [← pow_mul, ← zpow_natCast zeta (x i * (p i : ℕ))]
      congr 1
      push_cast
      ring
    rwa [heq]
  have hoff : ∀ p ∈ F, p ≠ p₀ →
      ∏ i, (∑ j ∈ Finset.range m,
        (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ j) = 0 := by
    intro p hp hne
    obtain ⟨i₀, hi₀⟩ : ∃ i, p i ≠ p₀ i := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    refine Finset.prod_eq_zero (Finset.mem_univ i₀)
      (sum_pow_zpow_eq_zero hzeta ?_)
    intro hdvd
    have habs : |(p i₀ : ℤ) - (p₀ i₀ : ℤ)| < (m : ℤ) := by
      rw [abs_lt]
      change -((D : ℤ) + 1) < (p i₀ : ℤ) - (p₀ i₀ : ℤ) ∧
        (p i₀ : ℤ) - (p₀ i₀ : ℤ) < (D : ℤ) + 1
      constructor <;> omega
    have hz := Int.eq_zero_of_abs_lt_dvd hdvd habs
    apply hi₀
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp hz
  have hdiag :
      ∏ i : Fin M, (∑ j ∈ Finset.range m,
        (zeta ^ ((p₀ i : ℤ) - (p₀ i : ℤ))) ^ j) =
        (m : ℂ) ^ M := by
    simp [Finset.prod_const, m]
  have hfourier :
      ell p₀ * (m : ℂ) ^ M =
        ∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x := by
    have hrw : ∀ p ∈ F,
        ell p * ∏ i, (∑ j ∈ Finset.range m,
            (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ j) =
          ∑ x ∈ states,
            (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) *
              (ell p * ∏ i, zeta ^ ((p i : ℤ) * (x i : ℤ))) := by
      intro p hp
      rw [Finset.prod_univ_sum, Finset.mul_sum]
      apply Finset.sum_congr
      · ext x
        simp only [states, Fintype.mem_piFinset]
      · intro x hx
        have hsplit : ∀ i : Fin M,
            (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ x i =
              zeta ^ (-((p₀ i : ℤ) * (x i : ℤ))) *
                zeta ^ ((p i : ℤ) * (x i : ℤ)) := by
          intro i
          rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hzeta0]
          congr 1
          ring
        rw [Finset.prod_congr rfl (fun i _ => hsplit i),
          Finset.prod_mul_distrib]
        ring
    calc
      ell p₀ * (m : ℂ) ^ M =
          ∑ p ∈ F, ell p * ∏ i, (∑ j ∈ Finset.range m,
            (zeta ^ ((p i : ℤ) - (p₀ i : ℤ))) ^ j) := by
        rw [Finset.sum_eq_single p₀]
        · rw [hdiag]
        · intro p hp hne
          rw [hoff p hp hne, mul_zero]
        · exact fun h => (h hp₀).elim
      _ = ∑ p ∈ F, ∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) *
            (ell p * ∏ i, zeta ^ ((p i : ℤ) * (x i : ℤ))) :=
        Finset.sum_congr rfl hrw
      _ = ∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
  have hcharNorm : ∀ x : Fin M → ℕ, ‖(∏ i : Fin M,
      zeta ^ (-((p₀ i : ℤ) * (x i : ℤ))))‖ = 1 := by
    intro x
    rw [norm_prod]
    have hzetaNorm : ‖zeta‖ = 1 := hzeta.norm'_eq_one hm0
    simp [norm_zpow, hzetaNorm]
  have hrhs :
      ‖∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x‖ ≤
        (m : ℝ) ^ M * epsilon := by
    calc
      ‖∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x‖ ≤
          ∑ x ∈ states,
            ‖(∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _x ∈ states, epsilon := by
        apply Finset.sum_le_sum
        intro x hx
        rw [norm_mul, hcharNorm]
        simpa using hstateBound x hx
      _ = (m : ℝ) ^ M * epsilon := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        simp [states, m]
  have hmul : ‖ell p₀‖ * (m : ℝ) ^ M ≤ (m : ℝ) ^ M * epsilon := by
    calc
      ‖ell p₀‖ * (m : ℝ) ^ M = ‖ell p₀ * (m : ℂ) ^ M‖ := by simp
      _ = ‖∑ x ∈ states,
          (∏ i, zeta ^ (-((p₀ i : ℤ) * (x i : ℤ)))) * faceValue x‖ :=
        congrArg norm hfourier
      _ ≤ (m : ℝ) ^ M * epsilon := hrhs
  have hmpos : 0 < (m : ℝ) ^ M := by positivity
  nlinarith

/-- Torsion-language recurrence transfers an eventual uniform bound on a finite moving face to
the same bound on every limiting Fourier coefficient. -/
theorem norm_face_weight_le_of_torsionLanguageUniversal
    {M D : ℕ} (u : ℕ → ℂ) (hu : TorsionLanguageUniversal u)
    (F : Finset (Fin M → Fin (D + 1)))
    (w : ℕ → (Fin M → Fin (D + 1)) → ℂ)
    (ell : (Fin M → Fin (D + 1)) → ℂ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hw : ∀ p ∈ F, Tendsto (fun q => w q p) atTop (𝓝 (ell p)))
    (hface : ∀ᶠ q : ℕ in atTop,
      ‖∑ p ∈ F, w q p *
        ∏ r : Fin M, u (q + (r : ℕ)) ^ (p r : ℕ)‖ ≤ epsilon) :
    ∀ p ∈ F, ‖ell p‖ ≤ epsilon := by
  apply norm_face_fin_weight_le_of_uniform_torsion_bound F ell hepsilon
  intro s hs
  obtain ⟨q, _hqmono, hqtop, hqword⟩ :=
    hu.exists_strictMono_occurrences (show 0 < D + 1 by omega) s hs
  have hterm : ∀ p ∈ F,
      Tendsto (fun k =>
        w (q k) p * ∏ r : Fin M, u (q k + (r : ℕ)) ^ (p r : ℕ))
        atTop (𝓝 (ell p * ∏ r : Fin M, s r ^ (p r : ℕ))) := by
    intro p hp
    simpa only [hqword] using
      (((hw p hp).comp hqtop).mul tendsto_const_nhds)
  have hsum := tendsto_finsetSum F (fun p hp => hterm p hp)
  exact le_of_tendsto hsum.norm (hqtop.eventually hface)

/-- An exhaustion of finite torsion faces with errors tending to zero cannot retain one fixed
nonzero limiting coefficient.  The window size and the selected representative may vary with
the exhaustion parameter. -/
theorem false_of_torsionLanguageUniversal_approximateFaces
    {D : ℕ} (u : ℕ → ℂ) (hu : TorsionLanguageUniversal u)
    (M : ℕ → ℕ)
    (F : ∀ R, Finset (Fin (M R) → Fin (D + 1)))
    (w : ∀ R, ℕ → (Fin (M R) → Fin (D + 1)) → ℂ)
    (ell : ∀ R, (Fin (M R) → Fin (D + 1)) → ℂ)
    (p₀ : ∀ R, Fin (M R) → Fin (D + 1))
    (epsilon : ℕ → ℝ)
    (hepsilon : ∀ R, 0 ≤ epsilon R)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0))
    (hp₀ : ∀ R, p₀ R ∈ F R)
    (hw : ∀ R, ∀ p ∈ F R,
      Tendsto (fun q => w R q p) atTop (𝓝 (ell R p)))
    (hface : ∀ R, ∀ᶠ q : ℕ in atTop,
      ‖∑ p ∈ F R, w R q p *
        ∏ r : Fin (M R), u (q + (r : ℕ)) ^ (p r : ℕ)‖ ≤ epsilon R)
    (ell₀ : ℂ) (hell₀ : ∀ R, ell R (p₀ R) = ell₀) (hell₀ne : ell₀ ≠ 0) :
    False := by
  have hbound : ∀ R, ‖ell₀‖ ≤ epsilon R := by
    intro R
    rw [← hell₀ R]
    exact norm_face_weight_le_of_torsionLanguageUniversal
      u hu (F R) (w R) (ell R) (hepsilon R) (hw R) (hface R) (p₀ R) (hp₀ R)
  have hzero : ‖ell₀‖ ≤ 0 :=
    ge_of_tendsto hepsilonZero (Eventually.of_forall hbound)
  exact hell₀ne (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg ell₀)))

/-- **Gaussian tail-lock compiler.**  If every finite-window face has a common nonzero limiting
coefficient and its exterior error is bounded by one fixed polynomially weighted lattice
Gaussian tail, torsion-language universality is impossible. -/
theorem false_of_torsionLanguageUniversal_gaussianTailLock
    (ι : Type) [Fintype ι] [Nonempty ι]
    {D J : ℕ} {B : ℝ} (hB : 0 < B) (Q₀ C : ℝ) (hC : 0 ≤ C)
    (u : ℕ → ℂ) (hu : TorsionLanguageUniversal u)
    (M : ℕ → ℕ)
    (F : ∀ R, Finset (Fin (M R) → Fin (D + 1)))
    (w : ∀ R, ℕ → (Fin (M R) → Fin (D + 1)) → ℂ)
    (ell : ∀ R, (Fin (M R) → Fin (D + 1)) → ℂ)
    (p₀ : ∀ R, Fin (M R) → Fin (D + 1))
    (hp₀ : ∀ R, p₀ R ∈ F R)
    (hw : ∀ R, ∀ p ∈ F R,
      Tendsto (fun q => w R q p) atTop (𝓝 (ell R p)))
    (hface : ∀ R, ∀ᶠ q : ℕ in atTop,
      ‖∑ p ∈ F R, w R q p *
        ∏ r : Fin (M R), u (q + (r : ℕ)) ^ (p r : ℕ)‖ ≤
        C * ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
          (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^ J *
            Real.exp (-B * (gaussianOffsetEnergy z.1 - Q₀)))
    (ell₀ : ℂ) (hell₀ : ∀ R, ell R (p₀ R) = ell₀) (hell₀ne : ell₀ ≠ 0) :
    False := by
  let epsilon : ℕ → ℝ := fun R =>
    C * ∑' z : {z : ι → ℤ // z ∉ integerLatticeBox ι R},
      (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^ J *
        Real.exp (-B * (gaussianOffsetEnergy z.1 - Q₀))
  have hepsilon : ∀ R, 0 ≤ epsilon R := by
    intro R
    exact mul_nonneg hC (tsum_nonneg fun _ => by positivity)
  have hepsilonZero : Tendsto epsilon atTop (𝓝 0) := by
    simpa only [epsilon, mul_zero] using
      (tendsto_maxPolynomial_gaussian_tsum_outside_box_zero
        ι J hB Q₀).const_mul C
  exact false_of_torsionLanguageUniversal_approximateFaces
    u hu M F w ell p₀ epsilon hepsilon hepsilonZero hp₀ hw hface
      ell₀ hell₀ hell₀ne

/-! ## Exclusion of arbitrary integer ADEs -/

/-- A nonzero integer-normalized ADE is incompatible with a full-support Gaussian magnitude and
a torsion-language-universal unit phase.  The least source, stable maximal-degree weight, complete
Gaussian exterior estimate, and approximate Fourier exhaustion are all constructed internally. -/
theorem false_of_integerADE_gaussian_torsionLanguageUniversal
    {B : ℝ} (hB : 0 < B)
    {F : PowerSeries ℂ} {u : ℕ → ℂ}
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(B * (i : ℝ) ^ 2)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ i, ‖u i‖ = 1)
    (hu : TorsionLanguageUniversal u)
    {n : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ) (hQ : Q ≠ 0)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0) :
    False := by
  classical
  have hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ 2)) := by
    intro i
    rw [hcoeff, norm_mul, huNorm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation
    F hb Q hQ hQint hrel
  obtain ⟨anchor, ha, haD, haMax⟩ :=
    exists_maxShiftCode_topDegree_anchor Q hDpos
  let D := jetMonomialDegree n anchor
  have hD : 0 < D := by simpa only [D, haD] using hDpos
  have hDmax : D = magnitudeMaxJetDegree n Q := by
    simpa only [D] using haD
  obtain ⟨S, H, R₀, a₀, ha₀, ell, hS, hHJ, hell,
      hstable, huniform⟩ :=
    exists_gaussianOffsetFace_maximal_stable_nonzero_leadingCoefficient
      ha (by simpa only [D] using hD) 0 (by simpa only [D] using hD)
  obtain ⟨P, htail⟩ :=
    exists_eventually_norm_gaussianFaceCluster_le_tail hB
      hcoeff huNorm hrel ha (by rfl)
      (by
        intro m hm hmD
        apply haMax m hm
        simpa only [D, haD] using hmD)
      hDmax hD hS ha₀ hHJ huniform
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  let Q₀ : ℝ := gaussianOffsetPatternEnergy a₀
  let J := magnitudeMaxJetOrder n Q + P
  let C := gaussianADEExteriorConstant n D Q B Q₀ P + 1
  let M : ℕ → ℕ := fun R => 2 * (R + R₀) + 1
  let Face : ∀ R, Finset (Fin (M R) → Fin (D + 1)) := fun R =>
    gaussianPolynomialPatternFace D S (R + R₀)
  let w : ∀ R, ℕ → (Fin (M R) → Fin (D + 1)) → ℂ :=
    fun R t p => gaussianFaceWeight n D 0 Q B Q₀ H (R + R₀)
      (t + (R + R₀)) p
  let ellFace : ∀ R, (Fin (M R) → Fin (D + 1)) → ℂ :=
    fun R p => gaussianFaceWeightLimit n D 0 Q B Q₀ H (R + R₀) p
  let p₀ : ∀ R, Fin (M R) → Fin (D + 1) := fun R =>
    gaussianOffsetPatternWindow a₀
      (gaussianOffsetFace_totalCount
        (gaussianOffsetFace_mono (show R₀ ≤ R + R₀ by omega) ha₀))
      (R + R₀)
  have hp₀ : ∀ R, p₀ R ∈ Face R := by
    intro R
    let haR := gaussianOffsetFace_mono
      (show R₀ ≤ R + R₀ by omega) ha₀
    simpa only [p₀, Face] using
      gaussianOffsetPatternWindow_mem_gaussianPolynomialPatternFace haR
  have hw : ∀ R, ∀ p ∈ Face R,
      Tendsto (fun t => w R t p) atTop (𝓝 (ellFace R p)) := by
    intro R p hp
    let K := R + R₀
    have hpData : ( ∑ r, (p r : ℕ)) = D ∧
        (polynomialPatternSourceSum p : ℤ) - (K : ℤ) * (D : ℤ) = S := by
      simpa only [Face, K] using mem_gaussianPolynomialPatternFace.mp hp
    let a := gaussianOffsetPatternOfWindow K p
    let haFace : a ∈ gaussianOffsetFace D S K :=
      gaussianOffsetPatternOfWindow_mem_face_centered p hpData.1 hpData.2
    have hback : gaussianOffsetPatternWindow a
        (gaussianOffsetFace_totalCount haFace) K = p := by
      simpa only [a, haFace] using
        gaussianOffsetPatternWindow_patternOfWindow_eq p hpData.1 hpData.2
    have hdegree := huniform K a haFace
    rw [hback] at hdegree
    simpa only [w, ellFace, K] using
      tendsto_gaussianFaceWeight Q B Q₀ p hdegree
  have hface : ∀ R, ∀ᶠ t : ℕ in atTop,
      ‖∑ p ∈ Face R, w R t p *
        ∏ r : Fin (M R), u (t + (r : ℕ)) ^ (p r : ℕ)‖ ≤
        C * ∑' z : {z : Fin D → ℤ // z ∉ integerLatticeBox (Fin D) R},
          (1 + (integerLatticeMaxNatAbs z.1 : ℝ)) ^ J *
            Real.exp (-(B / 2) * (gaussianOffsetEnergy z.1 - Q₀)) := by
    intro R
    simpa only [Face, w, M, C, J, Q₀] using htail R
  have hell₀ : ∀ R, ellFace R (p₀ R) = ell := by
    intro R
    let K := R + R₀
    let haR := gaussianOffsetFace_mono (show R₀ ≤ K by
      dsimp only [K]
      omega) ha₀
    have hcoeffStable := hstable K (by dsimp only [K]; omega)
    have henergy : gaussianWindowPatternEnergy
        (gaussianOffsetPatternWindow a₀
          (gaussianOffsetFace_totalCount haR) K) =
        gaussianOffsetPatternEnergy a₀ := by
      simpa only [gaussianWindowPatternEnergy] using
        gaussianOffsetPatternWindow_energy haR
    dsimp only [ellFace, p₀, gaussianFaceWeightLimit]
    change
      (polynomialPatternWeightPoly n D K 0 Q
        (gaussianOffsetPatternWindow a₀
          (gaussianOffsetFace_totalCount haR) K)).coeff H *
          (Real.exp (-B *
            ((gaussianWindowPatternEnergy
              (gaussianOffsetPatternWindow a₀
                (gaussianOffsetFace_totalCount haR) K) : ℝ) - Q₀)) : ℂ) = ell
    rw [hcoeffStable, henergy]
    simp only [Q₀, sub_self, mul_zero, neg_zero, Real.exp_zero,
      Complex.ofReal_one, mul_one]
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg
      (gaussianADEExteriorConstant_nonneg n D Q hB.le Q₀ P) zero_le_one
  exact false_of_torsionLanguageUniversal_gaussianTailLock
    (Fin D) (D := D) (J := J) (B := B / 2) (by linarith)
    Q₀ C hC u hu M Face w ellFace p₀ hp₀ hw hface
      ell hell₀ hell

/-! ## Entire Gaussian phase series -/

/-- Full-support Gaussian coefficients with an arbitrary complex phase. -/
def gaussianPhaseCoeff (B : ℝ) (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-(B * (n : ℝ) ^ 2)) : ℂ) * u n

theorem norm_gaussianPhaseCoeff
    (B : ℝ) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    ‖gaussianPhaseCoeff B u n‖ = Real.exp (-(B * (n : ℝ) ^ 2)) := by
  rw [gaussianPhaseCoeff, norm_mul, hu, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem gaussianPhaseCoeff_ne_zero
    (B : ℝ) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    gaussianPhaseCoeff B u n ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_gaussianPhaseCoeff B hu]
  exact (Real.exp_pos _).ne'

/-- Every unit-phase Gaussian coefficient series has infinite radius of convergence. -/
theorem gaussianPhaseSeries_radius_eq_top
    {B : ℝ} (hB : 0 < B) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) :
    (FormalMultilinearSeries.ofScalars ℂ (gaussianPhaseCoeff B u)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  let A : ℝ := Real.log ((r : ℝ) + 1) + 1
  have hA : 0 < A := by
    have hr : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      have := NNReal.coe_nonneg r
      linarith
    have hlog : 0 ≤ Real.log ((r : ℝ) + 1) := Real.log_nonneg hr
    dsimp [A]
    linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, A / B ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (A / B)
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hlarge] with n hn
  rw [FormalMultilinearSeries.ofScalars_norm]
  rw [norm_gaussianPhaseCoeff B hu]
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity))]
  have hr0 : 0 ≤ (r : ℝ) := NNReal.coe_nonneg r
  have hrplus : 0 < (r : ℝ) + 1 := by positivity
  have hrpow : (r : ℝ) ^ n ≤
      Real.exp ((n : ℝ) * Real.log ((r : ℝ) + 1)) := by
    calc
      (r : ℝ) ^ n ≤ ((r : ℝ) + 1) ^ n :=
        pow_le_pow_left₀ hr0 (by linarith) n
      _ = Real.exp (Real.log ((r : ℝ) + 1)) ^ n := by
        rw [Real.exp_log hrplus]
      _ = Real.exp ((n : ℝ) * Real.log ((r : ℝ) + 1)) := by
        rw [Real.exp_nat_mul]
  have hBn : A ≤ (n : ℝ) * B := (div_le_iff₀ hB).mp hn
  have hquadratic : (n : ℝ) * A ≤ B * (n : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hBn (Nat.cast_nonneg n)
    nlinarith
  calc
    Real.exp (-(B * (n : ℝ) ^ 2)) * (r : ℝ) ^ n
        ≤ Real.exp (-(B * (n : ℝ) ^ 2)) *
            Real.exp ((n : ℝ) * Real.log ((r : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hrpow (Real.exp_pos _).le
    _ = Real.exp (-(B * (n : ℝ) ^ 2) +
        (n : ℝ) * Real.log ((r : ℝ) + 1)) := by rw [Real.exp_add]
    _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (by
      dsimp [A] at hquadratic
      linarith)

/-- The entire function determined by the Gaussian coefficient series. -/
def gaussianPhaseFunction (B : ℝ) (u : ℕ → ℂ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (gaussianPhaseCoeff B u)

theorem gaussianPhaseFunction_eq_tsum
    (B : ℝ) (u : ℕ → ℂ) (z : ℂ) :
    gaussianPhaseFunction B u z =
      ∑' n, gaussianPhaseCoeff B u n * z ^ n := by
  simpa [gaussianPhaseFunction, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (gaussianPhaseCoeff B u) z)

/-- The Gaussian phase series is analytic on the whole complex plane. -/
theorem analyticOnNhd_gaussianPhaseFunction
    {B : ℝ} (hB : 0 < B) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) :
    AnalyticOnNhd ℂ (gaussianPhaseFunction B u) Set.univ := by
  let p := FormalMultilinearSeries.ofScalars ℂ (gaussianPhaseCoeff B u)
  have hr : p.radius = ⊤ := gaussianPhaseSeries_radius_eq_top hB hu
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  simpa [gaussianPhaseFunction, p, hr] using hp.analyticOnNhd

theorem contDiff_gaussianPhaseFunction
    {B : ℝ} (hB : 0 < B) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) :
    ContDiff ℂ (⊤ : ℕ∞) (gaussianPhaseFunction B u) :=
  (analyticOnNhd_gaussianPhaseFunction hB hu).contDiff

/-- The Taylor coefficients of the constructed entire function are exactly the prescribed
Gaussian-phase coefficients. -/
theorem taylorPS_gaussianPhaseFunction
    {B : ℝ} (hB : 0 < B) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (gaussianPhaseFunction B u)) =
      gaussianPhaseCoeff B u n := by
  let p := FormalMultilinearSeries.ofScalars ℂ (gaussianPhaseCoeff B u)
  have hr : p.radius = ⊤ := gaussianPhaseSeries_radius_eq_top hB hu
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have hiter := hp.iteratedFDeriv_eq_sum_of_completeSpace
    (fun _ : Fin n => (1 : ℂ))
  have hiter' : iteratedDeriv n p.sum 0 =
      (n.factorial : ℂ) * gaussianPhaseCoeff B u n := by
    rw [iteratedDeriv_eq_iteratedFDeriv, hiter]
    simp [p, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  change PowerSeries.coeff n (taylorPS p.sum) = gaussianPhaseCoeff B u n
  rw [coeff_taylorPS, hiter']
  exact mul_div_cancel_left₀ (gaussianPhaseCoeff B u n)
    (by exact_mod_cast Nat.factorial_ne_zero n)

/-- **Gaussian torsion-language hypertranscendence.**  A smooth function with exact full-support
Taylor magnitudes `exp (-B n²)` and a torsion-language-universal unit phase satisfies no algebraic
differential equation. -/
theorem hypertranscendental_of_gaussian_torsionLanguageUniversal
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {B : ℝ} (hB : 0 < B) {u : ℕ → ℂ}
    (hcoeff : ∀ i, PowerSeries.coeff i (taylorPS f) =
      ((Real.exp (-(B * (i : ℝ) ^ 2)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ i, ‖u i‖ = 1)
    (hu : TorsionLanguageUniversal u) :
    Hypertranscendental f := by
  intro hDA
  obtain ⟨n, P, hP, hPfun⟩ := hDA
  have hjz : jetFun f n P = 0 := by
    funext z
    exact hPfun z
  have hformal : aeval (formalJets n (taylorPS f)) P = 0 := by
    rw [← taylorPS_jetFun f n hf P, hjz,
      show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl,
      taylorPS_const, map_zero]
  obtain ⟨n', Q, hQ, hQint, hrel⟩ :=
    formal_mahler_integer_normalization hP hformal
  exact false_of_integerADE_gaussian_torsionLanguageUniversal
    hB hcoeff huNorm hu Q hQ hQint hrel

/-- Every entire Gaussian series with a torsion-language-universal unit phase is
hypertranscendental. -/
theorem hypertranscendental_gaussianPhaseFunction
    {B : ℝ} (hB : 0 < B) {u : ℕ → ℂ}
    (huNorm : ∀ n, ‖u n‖ = 1) (hu : TorsionLanguageUniversal u) :
    Hypertranscendental (gaussianPhaseFunction B u) := by
  apply hypertranscendental_of_gaussian_torsionLanguageUniversal
    (contDiff_gaussianPhaseFunction hB huNorm) hB
  · intro n
    rw [taylorPS_gaussianPhaseFunction hB huNorm n]
    rfl
  · exact huNorm
  · exact hu

/-- The explicit concatenated universal torsion phase produces a concrete entire
hypertranscendental Gaussian series for every `B > 0`. -/
theorem hypertranscendental_universalUnit_gaussianPhaseFunction
    {B : ℝ} (hB : 0 < B) :
    Hypertranscendental
      (gaussianPhaseFunction B universalUnitTorsionPhase) :=
  hypertranscendental_gaussianPhaseFunction hB
    universalUnitTorsionPhase_norm
    universalUnitTorsionPhase_torsionLanguageUniversal

/-- The explicit unit-filled universal torsion phase therefore gives an entire Gaussian series
whose Taylor phase is torsion-language universal. -/
theorem exists_entire_gaussian_torsionLanguageUniversal
    (B : ℝ) (hB : 0 < B) :
    ∃ (f : ℂ → ℂ) (u : ℕ → ℂ),
      AnalyticOnNhd ℂ f Set.univ ∧
      (∀ n, PowerSeries.coeff n (taylorPS f) = gaussianPhaseCoeff B u n) ∧
      (∀ n, ‖u n‖ = 1) ∧ TorsionLanguageUniversal u := by
  refine ⟨gaussianPhaseFunction B universalUnitTorsionPhase,
    universalUnitTorsionPhase, ?_, ?_, universalUnitTorsionPhase_norm,
    universalUnitTorsionPhase_torsionLanguageUniversal⟩
  · exact analyticOnNhd_gaussianPhaseFunction hB universalUnitTorsionPhase_norm
  · intro n
    exact taylorPS_gaussianPhaseFunction hB universalUnitTorsionPhase_norm n

/-- Existence form of the Gaussian theorem: for every positive `B` there is an explicit entire
hypertranscendental function with full Gaussian Taylor support and torsion-language-universal
unit phase. -/
theorem exists_entire_hypertranscendental_gaussian_torsionLanguageUniversal
    (B : ℝ) (hB : 0 < B) :
    ∃ (f : ℂ → ℂ) (u : ℕ → ℂ),
      AnalyticOnNhd ℂ f Set.univ ∧ Hypertranscendental f ∧
      (∀ n, PowerSeries.coeff n (taylorPS f) = gaussianPhaseCoeff B u n) ∧
      (∀ n, ‖u n‖ = 1) ∧ TorsionLanguageUniversal u := by
  refine ⟨gaussianPhaseFunction B universalUnitTorsionPhase,
    universalUnitTorsionPhase,
    analyticOnNhd_gaussianPhaseFunction hB universalUnitTorsionPhase_norm,
    hypertranscendental_universalUnit_gaussianPhaseFunction hB, ?_,
    universalUnitTorsionPhase_norm,
    universalUnitTorsionPhase_torsionLanguageUniversal⟩
  intro n
  exact taylorPS_gaussianPhaseFunction hB universalUnitTorsionPhase_norm n

end

end GaloisForLFunctions
