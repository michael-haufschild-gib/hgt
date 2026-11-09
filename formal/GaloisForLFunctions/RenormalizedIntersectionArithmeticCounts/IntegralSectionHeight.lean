import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.DivisorRelationGeometry
import Mathlib.Data.Finset.Powerset

/-!
# Integral sections of the divisor quotient

Sections are integral representatives modulo the actual divisor relations. Their minimum
squared length is attained, and its minimizing sections are classified by subsets of the
squarefree vertices. Integer convexity gives an exact parallelogram defect. Doubling removes
that bounded residue defect and produces a quadratic height, equal to squared transverse
distance on the arithmetic gluing class. The logarithm of the finite minimizer count instead
has zero normalized doubling limit.
-/

noncomputable section
open Finset Matrix ArithmeticFunction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticDegenerationTheory

/-- The integral quotient before imposing the arithmetic gluing relation. -/
abbrev DivisorSectionClass (N : ℕ) (hN : 1 ≤ N) :=
  (Vertex N → ℤ) ⧸ divisorRelationLattice N hN

/-- Integral divisor inversion identifies the actual quotient with its primitive normal charge. -/
def divisorSectionChargeEquiv (N : ℕ) (hN : 1 ≤ N) :
    DivisorSectionClass N hN ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (divisorRelationLattice_eq_ker N hN)).trans
    ((divisorNormal N hN).quotKerEquivOfSurjective
      (fun k => ⟨Pi.single (poleVertex N hN) k, divisorNormal_pole N hN k⟩))

theorem divisorSectionChargeEquiv_mk (N : ℕ) (hN : 1 ≤ N) (v : Vertex N → ℤ) :
    divisorSectionChargeEquiv N hN ((divisorRelationLattice N hN).mkQ v) =
      divisorNormal N hN v := by
  change ((divisorNormal N hN).quotKerEquivOfSurjective
    (fun k => ⟨Pi.single (poleVertex N hN) k, divisorNormal_pole N hN k⟩))
      (Submodule.Quotient.mk v) = _
  rfl

/-- Squared integral length, valued in the natural numbers. -/
def divisorSectionEnergy (N : ℕ) (v : Vertex N → ℤ) : ℕ :=
  (∑ i, v i ^ 2).toNat

theorem divisorSectionEnergy_cast (N : ℕ) (v : Vertex N → ℤ) :
    (divisorSectionEnergy N v : ℤ) = ∑ i, v i ^ 2 :=
  Int.toNat_of_nonneg (sum_nonneg (fun i _ => sq_nonneg (v i)))

/-- The least squared length among actual integral representatives of a quotient class. -/
def divisorSectionMinimum (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) : ℕ :=
  sInf {m : ℕ | ∃ v : Vertex N → ℤ,
    (divisorRelationLattice N hN).mkQ v = c ∧ divisorSectionEnergy N v = m}

theorem divisorSectionEnergy_nonempty (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    {m : ℕ | ∃ v : Vertex N → ℤ,
      (divisorRelationLattice N hN).mkQ v = c ∧ divisorSectionEnergy N v = m}.Nonempty := by
  obtain ⟨v, rfl⟩ := (divisorRelationLattice N hN).mkQ_surjective c
  exact ⟨divisorSectionEnergy N v, v, rfl, rfl⟩

def divisorSquarefreeVertices (N : ℕ) : Finset (Vertex N) :=
  univ.filter (fun i => Squarefree i.val)

theorem mem_divisorSquarefreeVertices (N : ℕ) (i : Vertex N) :
    i ∈ divisorSquarefreeVertices N ↔ Squarefree i.val := by
  simp [divisorSquarefreeVertices]

theorem divisorSquarefreeVertices_card (N : ℕ) :
    (divisorSquarefreeVertices N).card = divisorSquarefreeCount N := by
  have h := divisorNormal_square_sum N
  simp_rw [ArithmeticFunction.moebius_sq] at h
  have hs : (∑ i : Vertex N, if Squarefree i.val then (1 : ℤ) else 0) =
      ((divisorSquarefreeVertices N).card : ℤ) := by
    simp [divisorSquarefreeVertices]
  rw [hs] at h
  exact_mod_cast h

private theorem consecutive_int_product_nonneg (z a : ℤ) :
    0 ≤ (z-a)*(z-a-1) := by
  by_cases h : z ≤ a
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  · exact mul_nonneg (by omega) (by omega)

/-- Coordinatewise integer convexity defect relative to two consecutive oriented values. -/
def divisorSectionDefect (N : ℕ) (a : ℤ) (v : Vertex N → ℤ) (i : Vertex N) : ℤ :=
  v i ^ 2 - (2*a+1)*moebius i.val*v i + a*(a+1)*moebius i.val ^ 2

theorem divisorSectionDefect_nonneg (N : ℕ) (a : ℤ) (v : Vertex N → ℤ) (i : Vertex N) :
    0 ≤ divisorSectionDefect N a v i := by
  by_cases hz : moebius i.val = 0
  · simpa [divisorSectionDefect, hz] using sq_nonneg (v i)
  · rcases moebius_ne_zero_iff_eq_or.mp hz with h | h
    · have ht := consecutive_int_product_nonneg (v i) a
      simp only [divisorSectionDefect, h]
      nlinarith only [ht]
    · have ht := consecutive_int_product_nonneg (-v i) a
      simp only [divisorSectionDefect, h]
      nlinarith only [ht]

theorem divisorSectionDefect_sum (N : ℕ) (hN : 1 ≤ N) (a : ℤ) (v : Vertex N → ℤ) :
    ∑ i, divisorSectionDefect N a v i =
      (divisorSectionEnergy N v : ℤ) - (2*a+1)*divisorNormal N hN v +
        a*(a+1)*(divisorSquarefreeCount N : ℤ) := by
  simp only [divisorSectionDefect, sum_add_distrib, sum_sub_distrib,
    divisorSectionEnergy_cast, divisorNormal_apply, mul_assoc, ← mul_sum,
    divisorNormal_square_sum]

/-- A balanced representative with upper value precisely on the selected squarefree vertices. -/
def divisorBalancedSection (N : ℕ) (a : ℤ) (A : Finset (Vertex N)) : Vertex N → ℤ :=
  fun i => moebius i.val * (a + if i ∈ A then 1 else 0)

private theorem sum_mem_indicator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (x : ℤ) :
    (∑ i, if i ∈ A then x else 0) = (A.card : ℤ)*x := by
  have hf : (univ.filter (fun i : ι => i ∈ A)) = A := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
  rw [← sum_filter, hf, sum_const, nsmul_eq_mul]

theorem divisorBalancedSection_normal (N : ℕ) (hN : 1 ≤ N) (a : ℤ)
    (A : Finset (Vertex N)) (hA : A ⊆ divisorSquarefreeVertices N) :
    divisorNormal N hN (divisorBalancedSection N a A) =
      (divisorSquarefreeCount N : ℤ)*a + A.card := by
  rw [divisorNormal_apply]
  have he (i : Vertex N) : moebius i.val * divisorBalancedSection N a A i =
      moebius i.val ^ 2 * a + if i ∈ A then 1 else 0 := by
    by_cases hi : i ∈ A
    · have hs : moebius i.val ^ 2 = 1 := by
        rw [ArithmeticFunction.moebius_sq,
          if_pos ((mem_divisorSquarefreeVertices N i).mp (hA hi))]
      simp only [divisorBalancedSection, if_pos hi]
      calc
        _ = moebius i.val ^ 2 * (a+1) := by ring
        _ = _ := by rw [hs]; ring
    · simp only [divisorBalancedSection, if_neg hi, add_zero]
      ring
  simp_rw [he]
  rw [sum_add_distrib, ← sum_mul, divisorNormal_square_sum]
  rw [sum_mem_indicator, mul_one]

theorem divisorBalancedSection_energy (N : ℕ) (a : ℤ)
    (A : Finset (Vertex N)) (hA : A ⊆ divisorSquarefreeVertices N) :
    (divisorSectionEnergy N (divisorBalancedSection N a A) : ℤ) =
      (divisorSquarefreeCount N : ℤ)*a^2 + (A.card : ℤ)*(2*a+1) := by
  rw [divisorSectionEnergy_cast]
  have he (i : Vertex N) : divisorBalancedSection N a A i ^ 2 =
      moebius i.val ^ 2 * a^2 + if i ∈ A then 2*a+1 else 0 := by
    by_cases hi : i ∈ A
    · have hs : moebius i.val ^ 2 = 1 := by
        rw [ArithmeticFunction.moebius_sq,
          if_pos ((mem_divisorSquarefreeVertices N i).mp (hA hi))]
      simp only [divisorBalancedSection, if_pos hi, mul_pow, hs]
      ring
    · simp only [divisorBalancedSection, if_neg hi, add_zero, mul_pow]
  simp_rw [he]
  rw [sum_add_distrib, ← sum_mul, divisorNormal_square_sum]
  rw [sum_mem_indicator]

theorem divisorSectionMinimum_le (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN)
    (v : Vertex N → ℤ) (hv : (divisorRelationLattice N hN).mkQ v = c) :
    divisorSectionMinimum N hN c ≤ divisorSectionEnergy N v :=
  Nat.sInf_le ⟨v, hv, rfl⟩

theorem divisorSectionMinimum_attained (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    ∃ v : Vertex N → ℤ, (divisorRelationLattice N hN).mkQ v = c ∧
      divisorSectionEnergy N v = divisorSectionMinimum N hN c :=
  Nat.sInf_mem (divisorSectionEnergy_nonempty N hN c)

theorem divisorSectionMinimum_eq_balanced (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) (a : ℤ) (A : Finset (Vertex N))
    (hA : A ⊆ divisorSquarefreeVertices N)
    (hk : divisorSectionChargeEquiv N hN c = (divisorSquarefreeCount N : ℤ)*a + A.card) :
    (divisorSectionMinimum N hN c : ℤ) =
      (divisorSquarefreeCount N : ℤ)*a^2 + (A.card : ℤ)*(2*a+1) := by
  have hv : (divisorRelationLattice N hN).mkQ (divisorBalancedSection N a A) = c := by
    apply (divisorSectionChargeEquiv N hN).injective
    rw [divisorSectionChargeEquiv_mk, divisorBalancedSection_normal N hN a A hA, hk]
  have hupper := divisorSectionMinimum_le N hN c (divisorBalancedSection N a A) hv
  have hupperz : (divisorSectionMinimum N hN c : ℤ) ≤
      (divisorSectionEnergy N (divisorBalancedSection N a A) : ℤ) := by exact_mod_cast hupper
  rw [divisorBalancedSection_energy N a A hA] at hupperz
  obtain ⟨w, hw, hwe⟩ := divisorSectionMinimum_attained N hN c
  have hnw : divisorNormal N hN w = divisorSectionChargeEquiv N hN c := by
    rw [← divisorSectionChargeEquiv_mk N hN w, hw]
  have hlow := sum_nonneg (fun i (_ : i ∈ (univ : Finset (Vertex N))) =>
    divisorSectionDefect_nonneg N a w i)
  rw [divisorSectionDefect_sum N hN, hnw, hk, hwe] at hlow
  exact le_antisymm hupperz (by nlinarith only [hlow])

theorem divisorSectionMinimum_formula (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    (divisorSectionMinimum N hN c : ℤ) =
      (divisorSquarefreeCount N : ℤ) *
        (divisorSectionChargeEquiv N hN c / divisorSquarefreeCount N)^2 +
      (divisorSectionChargeEquiv N hN c % divisorSquarefreeCount N) *
        (2*(divisorSectionChargeEquiv N hN c / divisorSquarefreeCount N)+1) := by
  let k := divisorSectionChargeEquiv N hN c
  let q : ℤ := divisorSquarefreeCount N
  have hq : 0 < q := by
    change (0 : ℤ) < divisorSquarefreeCount N
    exact_mod_cast divisorSquarefreeCount_pos N hN
  have hr0 : 0 ≤ k % q := Int.emod_nonneg k hq.ne'
  have hrl : k % q < q := Int.emod_lt_of_pos k hq
  have hrN : (k % q).toNat ≤ (divisorSquarefreeVertices N).card := by
    rw [divisorSquarefreeVertices_card]
    have hz : ((k % q).toNat : ℤ) ≤ (divisorSquarefreeCount N : ℤ) := by
      rw [Int.toNat_of_nonneg hr0]
      exact hrl.le
    exact_mod_cast hz
  obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq hrN
  have hcardz : (A.card : ℤ) = k % q := by
    rw [hcard, Int.toNat_of_nonneg hr0]
  have hk : divisorSectionChargeEquiv N hN c =
      (divisorSquarefreeCount N : ℤ) * (k/q) + A.card := by
    rw [hcardz]
    simpa only [add_comm] using (Int.emod_add_mul_ediv k q).symm
  have h := divisorSectionMinimum_eq_balanced N hN c (k/q) A hA hk
  rw [hcardz] at h
  exact h

def divisorSectionFloor (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) : ℤ :=
  divisorSectionChargeEquiv N hN c / divisorSquarefreeCount N

def divisorSectionRemainder (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) : ℕ :=
  (divisorSectionChargeEquiv N hN c % divisorSquarefreeCount N).toNat

theorem divisorSectionRemainder_cast (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) :
    (divisorSectionRemainder N hN c : ℤ) =
      divisorSectionChargeEquiv N hN c % divisorSquarefreeCount N := by
  apply Int.toNat_of_nonneg
  apply Int.emod_nonneg
  exact_mod_cast (divisorSquarefreeCount_pos N hN).ne'

theorem divisorSectionDivision (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) :
    divisorSectionChargeEquiv N hN c =
      (divisorSquarefreeCount N : ℤ)*divisorSectionFloor N hN c +
        divisorSectionRemainder N hN c := by
  rw [divisorSectionRemainder_cast]
  simpa only [divisorSectionFloor, add_comm] using
    (Int.emod_add_mul_ediv (divisorSectionChargeEquiv N hN c) (divisorSquarefreeCount N)).symm

theorem divisorSectionMinimum_balanced_formula (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    (divisorSectionMinimum N hN c : ℤ) =
      (divisorSquarefreeCount N : ℤ)*(divisorSectionFloor N hN c)^2 +
      (divisorSectionRemainder N hN c : ℤ)*(2*divisorSectionFloor N hN c+1) := by
  rw [divisorSectionRemainder_cast]
  exact divisorSectionMinimum_formula N hN c

theorem divisorSection_mk_eq_iff (N : ℕ) (hN : 1 ≤ N)
    (v : Vertex N → ℤ) (c : DivisorSectionClass N hN) :
    (divisorRelationLattice N hN).mkQ v = c ↔
      divisorNormal N hN v = divisorSectionChargeEquiv N hN c := by
  rw [← divisorSectionChargeEquiv_mk N hN v]
  exact (divisorSectionChargeEquiv N hN).injective.eq_iff.symm

theorem divisorSectionDefect_eq_zero_iff (N : ℕ) (a : ℤ) (v : Vertex N → ℤ)
    (i : Vertex N) :
    divisorSectionDefect N a v i = 0 ↔
      (moebius i.val = 0 → v i = 0) ∧
      (moebius i.val ≠ 0 → moebius i.val*v i = a ∨ moebius i.val*v i = a+1) := by
  by_cases hz : moebius i.val = 0
  · simp [divisorSectionDefect, hz]
  · rcases moebius_ne_zero_iff_eq_or.mp hz with h | h
    · have he : divisorSectionDefect N a v i = (v i-a)*(v i-a-1) := by
        simp only [divisorSectionDefect, h]
        ring
      rw [he, mul_eq_zero]
      simp only [h, one_ne_zero, false_implies, one_mul, true_and]
      omega
    · have he : divisorSectionDefect N a v i = (-v i-a)*(-v i-a-1) := by
        simp only [divisorSectionDefect, h]
        ring
      rw [he, mul_eq_zero]
      simp only [h, neg_ne_zero, neg_one_mul]
      omega

/-- Actual integral representatives attaining the least squared length. -/
def MinimumDivisorSection (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) :=
  {v : Vertex N → ℤ // (divisorRelationLattice N hN).mkQ v = c ∧
    divisorSectionEnergy N v = divisorSectionMinimum N hN c}

theorem minimumDivisorSection_balanced (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) (v : MinimumDivisorSection N hN c) (i : Vertex N) :
    (moebius i.val = 0 → v.val i = 0) ∧
      (moebius i.val ≠ 0 →
        moebius i.val*v.val i = divisorSectionFloor N hN c ∨
        moebius i.val*v.val i = divisorSectionFloor N hN c+1) := by
  apply (divisorSectionDefect_eq_zero_iff N _ v.val i).mp
  have hs : ∑ i, divisorSectionDefect N (divisorSectionFloor N hN c) v.val i = 0 := by
    rw [divisorSectionDefect_sum N hN,
      (divisorSection_mk_eq_iff N hN v.val c).mp v.property.1, v.property.2,
      divisorSectionMinimum_balanced_formula, divisorSectionDivision N hN c]
    ring
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (univ : Finset (Vertex N))) =>
      divisorSectionDefect_nonneg N _ v.val j)).mp hs i (mem_univ i)

theorem moebius_ne_zero_iff_mem_divisorSquarefreeVertices (N : ℕ) (i : Vertex N) :
    moebius i.val ≠ 0 ↔ i ∈ divisorSquarefreeVertices N := by
  rw [mem_divisorSquarefreeVertices]
  have hs := ArithmeticFunction.moebius_sq (n := i.val)
  by_cases hsf : Squarefree i.val
  · simp only [if_pos hsf] at hs
    have hz : moebius i.val ≠ 0 := by
      intro hz
      rw [hz] at hs
      norm_num at hs
    exact ⟨fun _ => hsf, fun _ => hz⟩
  · simp only [if_neg hsf] at hs
    have hz : moebius i.val = 0 := sq_eq_zero_iff.mp hs
    exact ⟨fun hn => (hn hz).elim, fun hh => (hsf hh).elim⟩

def divisorBalancedSupport (N : ℕ) (a : ℤ) (v : Vertex N → ℤ) : Finset (Vertex N) :=
  (divisorSquarefreeVertices N).filter (fun i => moebius i.val*v i = a+1)

theorem divisorBalancedSupport_subset (N : ℕ) (a : ℤ) (v : Vertex N → ℤ) :
    divisorBalancedSupport N a v ⊆ divisorSquarefreeVertices N := filter_subset _ _

theorem divisorBalancedSupport_reconstruct (N : ℕ) (a : ℤ) (v : Vertex N → ℤ)
    (hv : ∀ i, (moebius i.val = 0 → v i = 0) ∧
      (moebius i.val ≠ 0 → moebius i.val*v i = a ∨ moebius i.val*v i = a+1)) :
    v = divisorBalancedSection N a (divisorBalancedSupport N a v) := by
  funext i
  by_cases hz : moebius i.val = 0
  · simp [divisorBalancedSection, hz, (hv i).1 hz]
  · have hsf := (moebius_ne_zero_iff_mem_divisorSquarefreeVertices N i).mp hz
    have hs : moebius i.val ^ 2 = 1 := by
      rw [ArithmeticFunction.moebius_sq,
        if_pos ((mem_divisorSquarefreeVertices N i).mp hsf)]
    have hi : v i = moebius i.val * (moebius i.val*v i) := by
      calc
        _ = moebius i.val ^ 2*v i := by rw [hs, one_mul]
        _ = _ := by ring
    by_cases hm : i ∈ divisorBalancedSupport N a v
    · have hu := (mem_filter.mp hm).2
      rw [hi, hu]
      simp only [divisorBalancedSection, if_pos hm]
    · have hl : moebius i.val*v i = a := by
        rcases (hv i).2 hz with h | h
        · exact h
        · exact (hm (mem_filter.mpr ⟨hsf, h⟩)).elim
      rw [hi, hl]
      simp only [divisorBalancedSection, if_neg hm, add_zero]

theorem divisorBalancedSupport_balanced (N : ℕ) (a : ℤ) (A : Finset (Vertex N))
    (hA : A ⊆ divisorSquarefreeVertices N) :
    divisorBalancedSupport N a (divisorBalancedSection N a A) = A := by
  ext i
  by_cases hi : i ∈ A
  · have hsf := hA hi
    have hs : moebius i.val ^ 2 = 1 := by
      rw [ArithmeticFunction.moebius_sq,
        if_pos ((mem_divisorSquarefreeVertices N i).mp hsf)]
    have he : moebius i.val*divisorBalancedSection N a A i = a+1 := by
      simp only [divisorBalancedSection, if_pos hi]
      calc
        _ = moebius i.val ^ 2*(a+1) := by ring
        _ = _ := by rw [hs, one_mul]
    simp [divisorBalancedSupport, hi, hsf, he]
  · constructor
    · intro hm
      obtain ⟨hsf, hu⟩ := mem_filter.mp hm
      have hs : moebius i.val ^ 2 = 1 := by
        rw [ArithmeticFunction.moebius_sq,
          if_pos ((mem_divisorSquarefreeVertices N i).mp hsf)]
      have he : moebius i.val*divisorBalancedSection N a A i = a := by
        simp only [divisorBalancedSection, if_neg hi, add_zero]
        calc
          _ = moebius i.val ^ 2*a := by ring
          _ = _ := by rw [hs, one_mul]
      rw [he] at hu
      omega
    · exact fun h => (hi h).elim

theorem minimumDivisorSection_support_card (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) (v : MinimumDivisorSection N hN c) :
    (divisorBalancedSupport N (divisorSectionFloor N hN c) v.val).card =
      divisorSectionRemainder N hN c := by
  have he := divisorBalancedSupport_reconstruct N _ v.val
    (minimumDivisorSection_balanced N hN c v)
  have hn := congrArg (divisorNormal N hN) he
  rw [(divisorSection_mk_eq_iff N hN v.val c).mp v.property.1,
    divisorBalancedSection_normal N hN _ _ (divisorBalancedSupport_subset N _ v.val)] at hn
  have hd := divisorSectionDivision N hN c
  have hcard : ((divisorBalancedSupport N (divisorSectionFloor N hN c) v.val).card : ℤ) =
      (divisorSectionRemainder N hN c : ℤ) := by linarith only [hn, hd]
  exact_mod_cast hcard

/-- Minimizing sections correspond exactly to subsets of the prescribed residue cardinality. -/
def minimumDivisorSectionEquiv (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) :
    MinimumDivisorSection N hN c ≃
      ↥((divisorSquarefreeVertices N).powersetCard (divisorSectionRemainder N hN c)) where
  toFun v := ⟨divisorBalancedSupport N (divisorSectionFloor N hN c) v.val,
    mem_powersetCard.mpr ⟨divisorBalancedSupport_subset N _ v.val,
      minimumDivisorSection_support_card N hN c v⟩⟩
  invFun A := by
    have hA := (mem_powersetCard.mp A.property).1
    have hcard := (mem_powersetCard.mp A.property).2
    refine ⟨divisorBalancedSection N (divisorSectionFloor N hN c) A.val, ?_, ?_⟩
    · rw [divisorSection_mk_eq_iff, divisorBalancedSection_normal N hN _ _ hA,
        hcard, ← divisorSectionDivision N hN c]
    · apply Int.ofNat_inj.mp
      rw [divisorBalancedSection_energy N _ _ hA,
        divisorSectionMinimum_balanced_formula, hcard]
  left_inv v := by
    apply Subtype.ext
    exact (divisorBalancedSupport_reconstruct N _ v.val
      (minimumDivisorSection_balanced N hN c v)).symm
  right_inv A := by
    apply Subtype.ext
    exact divisorBalancedSupport_balanced N _ A.val (mem_powersetCard.mp A.property).1

/-- The cardinality of the actual minimum-section set, before its binomial evaluation. -/
def minimumDivisorSectionCount (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) : ℕ :=
  Nat.card (MinimumDivisorSection N hN c)

theorem minimumDivisorSectionCount_eq (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) :
    minimumDivisorSectionCount N hN c =
      Nat.choose (divisorSquarefreeCount N) (divisorSectionRemainder N hN c) := by
  rw [minimumDivisorSectionCount, Nat.card_congr (minimumDivisorSectionEquiv N hN c),
    Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard,
    divisorSquarefreeVertices_card]

private def balancedResidueEnergy (q k : ℤ) : ℤ :=
  q*(k/q)^2 + (k%q)*(2*(k/q)+1)

private theorem balancedResidueEnergy_scaled (q k : ℤ) :
    q*balancedResidueEnergy q k = k^2 + (k%q)*(q-k%q) := by
  calc
    _ = (q*(k/q)+k%q)^2 + (k%q)*(q-k%q) := by
      unfold balancedResidueEnergy
      ring
    _ = _ := by rw [add_comm (q*(k/q)) (k%q), Int.emod_add_mul_ediv]

/-- Four residue cases evaluate the periodic correction to the quadratic parallelogram law. -/
private theorem residue_parallelogram (q r s : ℤ) (_hq : 0 < q)
    (hr0 : 0 ≤ r) (hrq : r < q) (hs0 : 0 ≤ s) (hsq : s < q) :
    ((r+s)%q)*(q-(r+s)%q) + ((r-s)%q)*(q-(r-s)%q) -
      2*r*(q-r)-2*s*(q-s) =
        -2*q*min (min r (q-r)) (min s (q-s)) := by
  have hp : (r+s)%q = if r+s < q then r+s else r+s-q := by
    split_ifs with h
    · exact Int.emod_eq_of_lt (by omega) h
    · have hx : (r+s-q)%q = r+s-q := Int.emod_eq_of_lt (by omega) (by omega)
      have he : (r+s-q+q)%q = (r+s-q)%q := by simp [Int.add_emod]
      rw [show r+s-q+q = r+s by ring, hx] at he
      exact he
  have hm : (r-s)%q = if s ≤ r then r-s else r-s+q := by
    split_ifs with h
    · exact Int.emod_eq_of_lt (by omega) (by omega)
    · have hx : (r-s+q)%q = r-s+q := Int.emod_eq_of_lt (by omega) (by omega)
      have he : (r-s+q)%q = (r-s)%q := by simp
      rw [hx] at he
      exact he.symm
  rw [hp, hm]
  by_cases hsum : r+s < q <;> by_cases horder : s ≤ r
  · rw [if_pos hsum, if_pos horder]
    have hmin : min (min r (q-r)) (min s (q-s)) = s := by omega
    rw [hmin]
    ring
  · rw [if_pos hsum, if_neg horder]
    have hmin : min (min r (q-r)) (min s (q-s)) = r := by omega
    rw [hmin]
    ring
  · rw [if_neg hsum, if_pos horder]
    have hmin : min (min r (q-r)) (min s (q-s)) = q-r := by omega
    rw [hmin]
    ring
  · rw [if_neg hsum, if_neg horder]
    have hmin : min (min r (q-r)) (min s (q-s)) = q-s := by omega
    rw [hmin]
    ring

private theorem balancedResidueEnergy_parallelogram (q k l : ℤ) (hq : 0 < q) :
    balancedResidueEnergy q (k+l) + balancedResidueEnergy q (k-l) -
      2*balancedResidueEnergy q k - 2*balancedResidueEnergy q l =
        -2*min (min (k%q) (q-k%q)) (min (l%q) (q-l%q)) := by
  have hp := balancedResidueEnergy_scaled q (k+l)
  have hm := balancedResidueEnergy_scaled q (k-l)
  have hk := balancedResidueEnergy_scaled q k
  have hl := balancedResidueEnergy_scaled q l
  have hr := residue_parallelogram q (k%q) (l%q) hq
    (Int.emod_nonneg k hq.ne') (Int.emod_lt_of_pos k hq)
    (Int.emod_nonneg l hq.ne') (Int.emod_lt_of_pos l hq)
  have hpmod : (k+l)%q = (k%q+l%q)%q := Int.add_emod k l q
  have hmmod : (k-l)%q = (k%q-l%q)%q := Int.sub_emod k l q
  rw [← hpmod, ← hmmod] at hr
  apply mul_left_cancel₀ hq.ne'
  nlinarith only [hp, hm, hk, hl, hr]

private theorem divisorSectionMinimum_eq_residueEnergy (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    (divisorSectionMinimum N hN c : ℤ) =
      balancedResidueEnergy (divisorSquarefreeCount N) (divisorSectionChargeEquiv N hN c) :=
  divisorSectionMinimum_formula N hN c

/-- Distance of the charge residue to the nearest multiple of the squarefree count. -/
def divisorSectionResidueDistance (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) : ℤ :=
  min (divisorSectionRemainder N hN c : ℤ)
    ((divisorSquarefreeCount N : ℤ)-divisorSectionRemainder N hN c)

/-- The exact addition defect is negative twice the smaller residue distance. -/
theorem divisorSectionMinimum_parallelogram (N : ℕ) (hN : 1 ≤ N)
    (c d : DivisorSectionClass N hN) :
    (divisorSectionMinimum N hN (c+d) : ℤ) + divisorSectionMinimum N hN (c-d) -
      2*divisorSectionMinimum N hN c - 2*divisorSectionMinimum N hN d =
        -2*min (divisorSectionResidueDistance N hN c) (divisorSectionResidueDistance N hN d) := by
  simp only [divisorSectionMinimum_eq_residueEnergy, map_add, map_sub,
    divisorSectionResidueDistance, divisorSectionRemainder_cast]
  apply balancedResidueEnergy_parallelogram
  exact_mod_cast divisorSquarefreeCount_pos N hN

theorem divisorSectionMinimum_scaled (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    (divisorSquarefreeCount N : ℤ)*(divisorSectionMinimum N hN c : ℤ) =
      (divisorSectionChargeEquiv N hN c)^2 +
        (divisorSectionRemainder N hN c : ℤ)*
          ((divisorSquarefreeCount N : ℤ)-divisorSectionRemainder N hN c) := by
  rw [divisorSectionMinimum_eq_residueEnergy, divisorSectionRemainder_cast]
  exact balancedResidueEnergy_scaled _ _

theorem divisorSectionRemainder_lt (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) :
    divisorSectionRemainder N hN c < divisorSquarefreeCount N := by
  have hq : (0 : ℤ) < divisorSquarefreeCount N := by
    exact_mod_cast divisorSquarefreeCount_pos N hN
  have h := Int.emod_lt_of_pos (divisorSectionChargeEquiv N hN c) hq
  rw [← divisorSectionRemainder_cast N hN c] at h
  exact_mod_cast h

theorem divisorSectionMinimum_real_formula (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    (divisorSectionMinimum N hN c : ℝ) =
      (divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N +
        (divisorSectionRemainder N hN c : ℝ)*
          ((divisorSquarefreeCount N : ℝ)-divisorSectionRemainder N hN c) /
            divisorSquarefreeCount N := by
  have hq : (divisorSquarefreeCount N : ℝ) ≠ 0 := by
    exact_mod_cast (divisorSquarefreeCount_pos N hN).ne'
  have h := divisorSectionMinimum_scaled N hN c
  have hr : (divisorSquarefreeCount N : ℝ)*(divisorSectionMinimum N hN c : ℝ) =
      (divisorSectionChargeEquiv N hN c : ℝ)^2 +
        (divisorSectionRemainder N hN c : ℝ)*
          ((divisorSquarefreeCount N : ℝ)-divisorSectionRemainder N hN c) := by
    exact_mod_cast h
  rw [← add_div]
  apply (eq_div_iff hq).mpr
  exact (mul_comm _ _).trans hr

theorem divisorSectionMinimum_error_bounds (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    0 ≤ (divisorSectionMinimum N hN c : ℝ) -
      (divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N ∧
    (divisorSectionMinimum N hN c : ℝ) -
      (divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N ≤
        (divisorSquarefreeCount N : ℝ)/4 := by
  rw [divisorSectionMinimum_real_formula, add_sub_cancel_left]
  have hq : (0 : ℝ) < divisorSquarefreeCount N := by
    exact_mod_cast divisorSquarefreeCount_pos N hN
  have hr0 : (0 : ℝ) ≤ divisorSectionRemainder N hN c := Nat.cast_nonneg _
  have hrq : (divisorSectionRemainder N hN c : ℝ) ≤ divisorSquarefreeCount N := by
    exact_mod_cast (divisorSectionRemainder_lt N hN c).le
  refine ⟨div_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hrq)) hq.le, ?_⟩
  apply (div_le_iff₀ hq).mpr
  nlinarith only [sq_nonneg ((divisorSquarefreeCount N : ℝ)-
    2*(divisorSectionRemainder N hN c : ℝ))]

open Filter Topology

/-- Minimum section energy along doubling, normalized by the quadratic dilation factor. -/
def divisorSectionTateSequence (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN)
    (j : ℕ) : ℝ :=
  (divisorSectionMinimum N hN ((2^j : ℕ) • c) : ℝ) / (4 : ℝ)^j

theorem divisorSectionTateSequence_error (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) (j : ℕ) :
    0 ≤ divisorSectionTateSequence N hN c j -
      (divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N ∧
    divisorSectionTateSequence N hN c j -
      (divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N ≤
        ((divisorSquarefreeCount N : ℝ)/4)*(1/4 : ℝ)^j := by
  have hq : (0 : ℝ) < divisorSquarefreeCount N := by
    exact_mod_cast divisorSquarefreeCount_pos N hN
  have hp : (0 : ℝ) < (4 : ℝ)^j := pow_pos (by norm_num) j
  have hpow : ((2 : ℝ)^j)^2 = (4 : ℝ)^j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  have hc : (divisorSectionChargeEquiv N hN ((2^j : ℕ) • c) : ℝ)^2 =
      (4 : ℝ)^j*(divisorSectionChargeEquiv N hN c : ℝ)^2 := by
    have hz : divisorSectionChargeEquiv N hN ((2^j : ℕ) • c) =
        (2 : ℤ)^j*divisorSectionChargeEquiv N hN c := by
      rw [map_nsmul]
      simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hR : (divisorSectionChargeEquiv N hN ((2^j : ℕ) • c) : ℝ) =
        (2 : ℝ)^j*(divisorSectionChargeEquiv N hN c : ℝ) := by exact_mod_cast hz
    rw [hR, mul_pow, hpow]
  have he : divisorSectionTateSequence N hN c j -
      (divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N =
      ((divisorSectionMinimum N hN ((2^j : ℕ) • c) : ℝ) -
        (divisorSectionChargeEquiv N hN ((2^j : ℕ) • c) : ℝ)^2 /
          divisorSquarefreeCount N) / (4 : ℝ)^j := by
    rw [hc, divisorSectionTateSequence]
    field_simp [hp.ne', hq.ne']
  rw [he]
  have hb := divisorSectionMinimum_error_bounds N hN ((2^j : ℕ) • c)
  refine ⟨div_nonneg hb.1 hp.le, ?_⟩
  calc
    _ ≤ ((divisorSquarefreeCount N : ℝ)/4)/(4 : ℝ)^j :=
      div_le_div_of_nonneg_right hb.2 hp.le
    _ = _ := by simp only [div_eq_mul_inv, inv_pow, one_mul]

theorem tendsto_divisorSectionTateSequence (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    Tendsto (divisorSectionTateSequence N hN c) atTop
      (𝓝 ((divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N)) := by
  have hg : Tendsto (fun j : ℕ =>
      ((divisorSquarefreeCount N : ℝ)/4)*(1/4 : ℝ)^j) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (1/4 : ℝ)) (by norm_num)
    simpa using tendsto_const_nhds.mul h
  have he : Tendsto (fun j => divisorSectionTateSequence N hN c j -
      (divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N)
      atTop (𝓝 0) :=
    squeeze_zero (fun j => (divisorSectionTateSequence_error N hN c j).1)
      (fun j => (divisorSectionTateSequence_error N hN c j).2) hg
  have hf : (fun j => divisorSectionTateSequence N hN c j -
      (divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N +
        (divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N) =
      divisorSectionTateSequence N hN c := by funext j; ring
  have ht := he.add_const ((divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N)
  rw [hf, zero_add] at ht
  exact ht

/-- The limit of normalized minimum section sizes, independent of its charge formula. -/
def divisorSectionTateHeight (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) : ℝ :=
  Filter.limUnder atTop (divisorSectionTateSequence N hN c)

theorem divisorSectionTateHeight_eq (N : ℕ) (hN : 1 ≤ N) (c : DivisorSectionClass N hN) :
    divisorSectionTateHeight N hN c =
      (divisorSectionChargeEquiv N hN c : ℝ)^2 / divisorSquarefreeCount N :=
  (tendsto_divisorSectionTateSequence N hN c).limUnder_eq

theorem divisorSectionTateHeight_parallelogram (N : ℕ) (hN : 1 ≤ N)
    (c d : DivisorSectionClass N hN) :
    divisorSectionTateHeight N hN (c+d) + divisorSectionTateHeight N hN (c-d) =
      2*divisorSectionTateHeight N hN c + 2*divisorSectionTateHeight N hN d := by
  simp only [divisorSectionTateHeight_eq, map_add, map_sub, Int.cast_add, Int.cast_sub]
  ring

theorem divisorSectionTateHeight_nsmul (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) (m : ℕ) :
    divisorSectionTateHeight N hN (m • c) = (m : ℝ)^2*divisorSectionTateHeight N hN c := by
  simp only [divisorSectionTateHeight_eq, map_nsmul, nsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast]
  ring

theorem divisorSectionMinimum_zero (N : ℕ) (hN : 1 ≤ N) :
    divisorSectionMinimum N hN 0 = 0 := by
  apply Int.ofNat_inj.mp
  rw [divisorSectionMinimum_formula, (divisorSectionChargeEquiv N hN).map_zero]
  simp

theorem divisorSectionResidueDistance_bounds (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    0 ≤ divisorSectionResidueDistance N hN c ∧
      2*divisorSectionResidueDistance N hN c ≤ (divisorSquarefreeCount N : ℤ) := by
  have hr0 : (0 : ℤ) ≤ divisorSectionRemainder N hN c := Int.natCast_nonneg _
  have hrq : (divisorSectionRemainder N hN c : ℤ) ≤ divisorSquarefreeCount N := by
    exact_mod_cast (divisorSectionRemainder_lt N hN c).le
  refine ⟨le_min hr0 (sub_nonneg.mpr hrq), ?_⟩
  have h1 := min_le_left (divisorSectionRemainder N hN c : ℤ)
    ((divisorSquarefreeCount N : ℤ)-divisorSectionRemainder N hN c)
  have h2 := min_le_right (divisorSectionRemainder N hN c : ℤ)
    ((divisorSquarefreeCount N : ℤ)-divisorSectionRemainder N hN c)
  change 2*min _ _ ≤ _
  linarith only [h1, h2]

theorem divisorSectionMinimum_doubling (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    (divisorSectionMinimum N hN ((2 : ℕ) • c) : ℤ) -
      4*divisorSectionMinimum N hN c = -2*divisorSectionResidueDistance N hN c := by
  have h := divisorSectionMinimum_parallelogram N hN c c
  rw [show c+c = (2 : ℕ) • c by rw [two_nsmul], sub_self,
    divisorSectionMinimum_zero, Nat.cast_zero, add_zero, min_self] at h
  linarith only [h]

theorem divisorSectionTateSequence_antitone (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) : Antitone (divisorSectionTateSequence N hN c) := by
  apply antitone_nat_of_succ_le
  intro j
  have hd := divisorSectionMinimum_doubling N hN ((2^j : ℕ) • c)
  have hr := (divisorSectionResidueDistance_bounds N hN ((2^j : ℕ) • c)).1
  have hi : (divisorSectionMinimum N hN ((2 : ℕ) • ((2^j : ℕ) • c)) : ℤ) ≤
      4*(divisorSectionMinimum N hN ((2^j : ℕ) • c) : ℤ) := by
    linarith only [hd, hr]
  have he : ((2^(j+1) : ℕ) • c) = (2 : ℕ) • ((2^j : ℕ) • c) := by
    rw [pow_succ, mul_comm (2^j) 2, mul_smul]
  have hR : (divisorSectionMinimum N hN ((2^(j+1) : ℕ) • c) : ℝ) ≤
      4*(divisorSectionMinimum N hN ((2^j : ℕ) • c) : ℝ) := by
    rw [he]
    exact_mod_cast hi
  have hp : (0 : ℝ) < (4 : ℝ)^j := pow_pos (by norm_num) j
  change _ / (4 : ℝ)^(j+1) ≤ _ / (4 : ℝ)^j
  apply (div_le_div_iff₀ (pow_pos (by norm_num) (j+1)) hp).mpr
  rw [show (4 : ℝ)^(j+1) = (4 : ℝ)^j*4 by rw [pow_succ]]
  nlinarith only [mul_le_mul_of_nonneg_right hR hp.le]

/-- The class of the actual arithmetic gluing column in the unglued divisor quotient. -/
def divisorGluingClass (N : ℕ) (hN : 1 ≤ N) : DivisorSectionClass N hN :=
  (divisorRelationLattice N hN).mkQ (integerGluingColumn N)

theorem divisorGluingClass_charge (N : ℕ) (hN : 1 ≤ N) :
    divisorSectionChargeEquiv N hN (divisorGluingClass N hN) = integerGluingCharge N := by
  rw [divisorGluingClass, divisorSectionChargeEquiv_mk]
  exact integerMoebius_pole_row N hN

theorem divisorGluingClass_tateHeight (N : ℕ) (hN : 1 ≤ N) :
    divisorSectionTateHeight N hN (divisorGluingClass N hN) =
      divisorTransverseDistance N (integerGluingRealColumn N)^2 := by
  rw [divisorSectionTateHeight_eq, divisorGluingClass_charge,
    divisorTransverseDistance_formula N hN, divisorRealNormal_gluing N hN]
  exact (Real.sq_sqrt (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))).symm

theorem divisorSectionEnergy_neg (N : ℕ) (v : Vertex N → ℤ) :
    divisorSectionEnergy N (-v) = divisorSectionEnergy N v := by
  simp only [divisorSectionEnergy, Pi.neg_apply, neg_sq]

theorem divisorSectionMinimum_neg (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    divisorSectionMinimum N hN (-c) = divisorSectionMinimum N hN c := by
  have hle (d : DivisorSectionClass N hN) :
      divisorSectionMinimum N hN (-d) ≤ divisorSectionMinimum N hN d := by
    obtain ⟨v, hv, he⟩ := divisorSectionMinimum_attained N hN d
    calc
      _ ≤ divisorSectionEnergy N (-v) :=
        divisorSectionMinimum_le N hN (-d) (-v) (by rw [map_neg, hv])
      _ = divisorSectionEnergy N v := divisorSectionEnergy_neg N v
      _ = _ := he
  exact le_antisymm (hle c) (by simpa only [neg_neg] using hle (-c))

theorem divisorSectionMinimum_eq_charge_of_nonneg (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN)
    (hk0 : 0 ≤ divisorSectionChargeEquiv N hN c)
    (hkq : divisorSectionChargeEquiv N hN c ≤ (divisorSquarefreeCount N : ℤ)) :
    (divisorSectionMinimum N hN c : ℤ) = divisorSectionChargeEquiv N hN c := by
  have hcard : (divisorSectionChargeEquiv N hN c).toNat ≤
      (divisorSquarefreeVertices N).card := by
    rw [divisorSquarefreeVertices_card]
    exact_mod_cast (show ((divisorSectionChargeEquiv N hN c).toNat : ℤ) ≤
      (divisorSquarefreeCount N : ℤ) by rw [Int.toNat_of_nonneg hk0]; exact hkq)
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hcard
  have hAcZ : (A.card : ℤ) = divisorSectionChargeEquiv N hN c := by
    rw [hAc, Int.toNat_of_nonneg hk0]
  have hk : divisorSectionChargeEquiv N hN c = (divisorSquarefreeCount N : ℤ)*0+A.card := by
    rw [mul_zero, zero_add, hAcZ]
  have h := divisorSectionMinimum_eq_balanced N hN c 0 A hA hk
  simpa only [zero_pow (by omega : 2 ≠ 0), mul_zero, zero_add, mul_one, hAcZ] using h

theorem divisorSectionMinimum_eq_abs_charge (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN)
    (hk : |divisorSectionChargeEquiv N hN c| ≤ (divisorSquarefreeCount N : ℤ)) :
    divisorSectionMinimum N hN c = (divisorSectionChargeEquiv N hN c).natAbs := by
  by_cases h0 : 0 ≤ divisorSectionChargeEquiv N hN c
  · have he := divisorSectionMinimum_eq_charge_of_nonneg N hN c h0
      ((le_abs_self _).trans hk)
    rw [← he]
    simp
  · have h0' : 0 ≤ divisorSectionChargeEquiv N hN (-c) := by rw [map_neg]; omega
    have hq' : divisorSectionChargeEquiv N hN (-c) ≤ (divisorSquarefreeCount N : ℤ) := by
      rw [map_neg]
      exact (neg_le_abs _).trans hk
    have he := divisorSectionMinimum_eq_charge_of_nonneg N hN (-c) h0' hq'
    have ha := congrArg Int.natAbs he
    simpa only [Int.natAbs_natCast, divisorSectionMinimum_neg, map_neg, Int.natAbs_neg] using ha

theorem integerGluingCharge_abs_le_squarefreeCount (N : ℕ) (hN : 1 ≤ N) :
    |integerGluingCharge N| ≤ (divisorSquarefreeCount N : ℤ) := by
  have he : (∑ i : Vertex N, moebius i.val*integerGluingColumn N i) = integerGluingCharge N := by
    have h : divisorNormal N hN (integerGluingColumn N) = integerGluingCharge N :=
      integerMoebius_pole_row N hN
    rw [divisorNormal_apply] at h
    exact h
  rw [← he]
  calc
    _ ≤ ∑ i : Vertex N, |moebius i.val*integerGluingColumn N i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Vertex N, moebius i.val ^ 2 := by
      apply sum_le_sum
      intro i _
      by_cases hz : moebius i.val = 0
      · simp [hz]
      · rcases moebius_ne_zero_iff_eq_or.mp hz with h | h <;>
          simp only [h, integerGluingColumn] <;> split_ifs <;> norm_num
    _ = _ := divisorNormal_square_sum N

/-- The minimum section size of the gluing class equals its integer quotient cardinality. -/
theorem divisorGluingClass_minimum_eq_count (N : ℕ) (hN : 1 ≤ N) :
    divisorSectionMinimum N hN (divisorGluingClass N hN) = integerGluingCount N := by
  rw [divisorSectionMinimum_eq_abs_charge N hN _ (by
    rw [divisorGluingClass_charge]
    exact integerGluingCharge_abs_le_squarefreeCount N hN),
    divisorGluingClass_charge, integerGluingCount_eq N hN]

theorem minimumDivisorSectionCount_pos (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) : 0 < minimumDivisorSectionCount N hN c := by
  letI : Fintype (MinimumDivisorSection N hN c) :=
    Fintype.ofEquiv _ (minimumDivisorSectionEquiv N hN c).symm
  obtain ⟨v, hv, he⟩ := divisorSectionMinimum_attained N hN c
  letI : Nonempty (MinimumDivisorSection N hN c) := ⟨⟨v, hv, he⟩⟩
  exact Nat.card_pos

theorem minimumDivisorSectionCount_le_pow (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    minimumDivisorSectionCount N hN c ≤ 2^(divisorSquarefreeCount N) := by
  have hsub : (divisorSquarefreeVertices N).powersetCard (divisorSectionRemainder N hN c) ⊆
      (divisorSquarefreeVertices N).powerset := by
    intro A hA
    exact mem_powerset.mpr (mem_powersetCard.mp hA).1
  have h := card_le_card hsub
  rw [card_powersetCard, card_powerset, divisorSquarefreeVertices_card] at h
  rw [minimumDivisorSectionCount_eq]
  exact h

theorem minimumDivisorSectionCount_log_bounds (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    0 ≤ Real.log (minimumDivisorSectionCount N hN c) ∧
      Real.log (minimumDivisorSectionCount N hN c) ≤
        (divisorSquarefreeCount N : ℝ)*Real.log 2 := by
  have hc := minimumDivisorSectionCount_pos N hN c
  refine ⟨Real.log_nonneg (by exact_mod_cast hc), ?_⟩
  have hu : (minimumDivisorSectionCount N hN c : ℝ) ≤
      (2 : ℝ)^(divisorSquarefreeCount N) := by
    exact_mod_cast minimumDivisorSectionCount_le_pow N hN c
  have hl := Real.log_le_log (show (0 : ℝ) < minimumDivisorSectionCount N hN c by
    exact_mod_cast hc) hu
  rw [Real.log_pow] at hl
  exact hl

/-- At fixed conductor, the logarithm of the minimizer count has zero quadratic Tate limit. -/
theorem tendsto_minimumDivisorSectionLogCount_zero (N : ℕ) (hN : 1 ≤ N)
    (c : DivisorSectionClass N hN) :
    Tendsto (fun j : ℕ =>
      Real.log (minimumDivisorSectionCount N hN ((2^j : ℕ) • c))/(4 : ℝ)^j)
      atTop (𝓝 0) := by
  have hgeom : Tendsto (fun j : ℕ =>
      ((divisorSquarefreeCount N : ℝ)*Real.log 2)*(1/4 : ℝ)^j) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (1/4 : ℝ)) (by norm_num)
    have hc : Tendsto (fun _ : ℕ => (divisorSquarefreeCount N : ℝ)*Real.log 2)
        atTop (𝓝 ((divisorSquarefreeCount N : ℝ)*Real.log 2)) := tendsto_const_nhds
    simpa only [mul_zero] using hc.mul hp
  apply squeeze_zero _ _ hgeom
  · intro j
    exact div_nonneg (minimumDivisorSectionCount_log_bounds N hN ((2^j : ℕ) • c)).1
      (pow_nonneg (by norm_num) j)
  · intro j
    have hu := div_le_div_of_nonneg_right
      (minimumDivisorSectionCount_log_bounds N hN ((2^j : ℕ) • c)).2
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) j)
    simpa only [div_eq_mul_inv, inv_pow, one_mul] using hu

#print axioms divisorSectionChargeEquiv
#print axioms divisorSectionDefect_sum
#print axioms divisorSectionMinimum_formula
#print axioms minimumDivisorSection_balanced
#print axioms minimumDivisorSectionEquiv
#print axioms minimumDivisorSectionCount_eq
#print axioms divisorSectionMinimum_parallelogram
#print axioms divisorSectionMinimum_error_bounds
#print axioms tendsto_divisorSectionTateSequence
#print axioms divisorSectionTateHeight_parallelogram
#print axioms divisorSectionTateHeight_nsmul
#print axioms divisorSectionMinimum_doubling
#print axioms divisorSectionTateSequence_antitone
#print axioms divisorGluingClass_tateHeight
#print axioms divisorSectionMinimum_eq_abs_charge
#print axioms divisorGluingClass_minimum_eq_count
#print axioms minimumDivisorSectionCount_log_bounds
#print axioms tendsto_minimumDivisorSectionLogCount_zero

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
