import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Synthesis

/-! # Exact mixed-prime calibrations for finite Gibbs reflection measurements -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Set MvPolynomial
open _root_.HTGeometry (finiteGibbsStateWeight)

/-- A resonant order admits a finite nontrivial rational linear relation among the shell powers. -/
def Resonant (t : ℝ) := ¬LinearIndependent ℚ (shellPower t)

theorem resonant_iff_prime_dependence (t : ℝ) :
    Resonant t ↔ ¬AlgebraicIndependent ℚ (coordinates t) := (independent_iff ℚ t).not.symm

theorem resonant_iff_polynomial (t : ℝ) :
    Resonant t ↔ ∃ P : PolynomialRing, P ≠ 0 ∧ value t P=0 := by
  rw [Resonant,← LinearIndependent.iff_fractionRing ℤ ℚ,← independent_iff,algebraicIndependent_iff]
  push Not
  exact exists_congr fun P => and_comm

private theorem annihilator (T : Finset ℝ) (h : ∀ t ∈ T, Resonant t) :
    ∃ P : PolynomialRing, P ≠ 0 ∧ ∀ t ∈ T, value t P=0 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1,one_ne_zero,fun _ ht => (notMem_empty _ ht).elim⟩
  | insert t T _ ih =>
    obtain ⟨P,hP,zeros⟩ := ih fun u hu => h u (mem_insert_of_mem hu)
    obtain ⟨Q,hQ,root⟩ := (resonant_iff_polynomial t).mp (h t (mem_insert_self _ _))
    refine ⟨Q*P,mul_ne_zero hQ hP,fun u hu => ?_⟩
    rw [map_mul]
    rcases mem_insert.mp hu with rfl | m
    · rw [root,zero_mul]
    · rw [zeros u m,mul_zero]

/-- All independently resonant positive orders of a finite schedule can occur
on one asymmetric integer spectrum. -/
theorem schedule_iff (T : Finset ℝ) (pos : ∀ t ∈ T, 0<t) :
    (∃ (n : ℕ) (a : Fin n → ℕ+), ¬Reflects (energy ∘ a) ∧ ∀ t ∈ T, agrees (energy ∘ a) t) ↔
      ∀ t ∈ T, Resonant t := by
  constructor
  · rintro ⟨n,a,asym,hit⟩ t ht
    exact (resonant_iff_polynomial t).mpr ⟨certificate a,certificate_ne_zero a asym,
      (certificate_root a (size_of_asymmetric a asym) t).mpr (hit t ht)⟩
  · intro h
    obtain ⟨P,hP,zeros⟩ := annihilator T h
    obtain ⟨n,a,asym,hit⟩ := polynomial_spectrum P hP
    exact ⟨n,a,asym,fun t ht => (hit t (pos t ht)).mpr (Or.inl (zeros t ht))⟩

/-- The genuinely bad ratios depend only on the two arithmetic resonances,
which can initially come from unrelated prime supports or spectra. -/
theorem exceptional_iff (r : ℝ) : r ∈ exceptional energy ↔
    ∃ x y : ℝ, 0<x ∧ 0<y ∧ Resonant x ∧ Resonant y ∧ x/y=r := by
  classical
  constructor
  · intro h
    obtain ⟨⟨n,a⟩,⟨x,y⟩,⟨hx,hy⟩,eq⟩ := mem_iUnion.mp h
    change x ∈ blind (energy ∘ a) at hx
    change y ∈ blind (energy ∘ a) at hy
    have T : ∀ u ∈ ({x,y} : Finset ℝ), 0<u := by simpa using And.intro hx.1 hy.1
    have hit := (schedule_iff {x,y} T).mp ⟨n,a,hx.2.2,by
      simpa using And.intro hx.2.1 hy.2.1⟩
    exact ⟨x,y,hx.1,hy.1,hit x (mem_insert_self _ _),hit y (mem_insert_of_mem (mem_singleton_self y)),eq⟩
  · rintro ⟨x,y,hx,hy,rx,ry,eq⟩
    obtain ⟨n,a,asym,hit⟩ := (schedule_iff {x,y} (by simpa using And.intro hx hy)).mpr
      (by simpa using And.intro rx ry)
    exact mem_iUnion.mpr ⟨⟨n,a⟩,⟨(x,y),⟨⟨hx,hit x (by simp),asym⟩,⟨hy,hit y (by simp),asym⟩⟩,eq⟩⟩

/-- At fixed nonzero damping, a finite family detects every asymmetric spectrum
exactly when one of its rescaled orders is universally detecting by itself. -/
theorem fixed_damping_iff (d : ℝ) (hd : d ≠ 0) (T : Finset ℝ) (pos : ∀ t ∈ T, 0<t) :
    (∀ n (a : Fin n → ℕ+),
      (∀ t ∈ T, lawOrder (finiteGibbsStateWeight d (energy ∘ a)) t) → Reflects (energy ∘ a)) ↔
      ∃ t ∈ T, ¬Resonant (t*|d|) := by
  classical
  let f (t : ℝ) := t*|d|
  have eq (n : ℕ) (a : Fin n → ℕ+) :
      (∀ t ∈ T, lawOrder (finiteGibbsStateWeight d (energy ∘ a)) t) ↔
        ∀ u ∈ T.image f, agrees (energy ∘ a) u := by
    rw [Finset.forall_mem_image]
    apply forall₂_congr
    intro t ht
    rw [gibbs_order,← agrees_abs (energy ∘ a) (t*d),abs_mul,abs_of_pos (pos t ht)]
  have positive : ∀ u ∈ T.image f, 0<u := by
    rw [Finset.forall_mem_image]
    exact fun t ht => mul_pos (pos t ht) (abs_pos.mpr hd)
  constructor
  · intro all
    by_contra! bad
    obtain ⟨n,a,asym,pass⟩ := (schedule_iff (T.image f) positive).mpr (Finset.forall_mem_image.mpr (fun {_} ht => bad _ ht))
    exact asym (all n a ((eq n a).mpr pass))
  · rintro ⟨t,ht,detect⟩ n a pass
    by_contra asym
    have bad := (schedule_iff (T.image f) positive).mp ⟨n,a,asym,(eq n a).mp pass⟩
    exact detect (bad (f t) (mem_image_of_mem f ht))

/-- Exact arithmetic criterion for two readings of one Gibbs law to detect the
isometric divisor split across every finite integer-shell spectrum. -/
theorem split_law_iff {r : ℝ} (hr : 0<r) :
    (∀ n (a : Fin n → ℕ+) (s : ℂ),
      let E := energy ∘ a
      let P := finiteGibbsStateWeight (2*s.re-1) E
      lawOrder P 1 ∧ lawOrder P r ↔
        (∃ V : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, V f x=split s f x) ∨ Reflects E) ↔
    ¬∃ x y : ℝ, 0<x ∧ 0<y ∧ Resonant x ∧ Resonant y ∧ x/y=r := by
  rw [← exceptional_iff]
  have mid (u : ℝ) : 2*u-1=0 ↔ u=1/2 := by constructor <;> intro h <;> linarith only [h]
  constructor
  · intro law
    apply (alphabet_iff energy hr).mp
    intro n a d
    have specific := law n a (((d+1)/2 : ℝ) : ℂ)
    dsimp only at specific
    rw [gibbs_order,gibbs_order,one_mul,split_isometric_iff,Complex.ofReal_re,
      ← mid,show 2*((d+1)/2)-1=d by ring] at specific
    exact specific
  · intro good n a s
    dsimp only
    rw [gibbs_order,gibbs_order,one_mul,split_isometric_iff,← mid]
    exact calibrated energy a hr good (2*s.re-1)

#print axioms split_law_iff
#print axioms resonant_iff_prime_dependence
#print axioms schedule_iff
#print axioms exceptional_iff
#print axioms fixed_damping_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
