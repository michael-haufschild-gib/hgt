import GaloisForLFunctions.RHTower.Sieve.VinogradovLinnikLifting
import GaloisForLFunctions.RHTower.Sieve.VinogradovDiagonalMoment
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.BigOperators

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def VinogradovCompatibleSignature (p k : ℕ)
    (h : (j : Fin k) → Fin (p ^ (j.val + 1))) :=
  {g : Fin k → ZMod (p ^ k) //
    ∀ j : Fin k, (g j).val % (p ^ (j.val + 1)) = (h j).val}

noncomputable instance vinogradovCompatibleSignatureFinite
    (p k : ℕ) [Fact p.Prime]
    (h : (j : Fin k) → Fin (p ^ (j.val + 1))) :
    Finite (VinogradovCompatibleSignature p k h) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance vinogradovCompatibleSignatureFintype
    (p k : ℕ) [Fact p.Prime]
    (h : (j : Fin k) → Fin (p ^ (j.val + 1))) :
    Fintype (VinogradovCompatibleSignature p k h) := Fintype.ofFinite _

def vinogradovCompatibleSignatureQuotientEmbedding
    {p k : ℕ} (hp : p.Prime)
    (h : (j : Fin k) → Fin (p ^ (j.val + 1))) :
    VinogradovCompatibleSignature p k h ↪
      ((j : Fin k) → Fin (p ^ (k - (j.val + 1)))) where
  toFun g j := by
    letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
    refine ⟨(g.1 j).val / (p ^ (j.val + 1)), ?_⟩
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp.pos _)]
    calc
      (g.1 j).val < p ^ k := ZMod.val_lt _
      _ = p ^ (k - (j.val + 1)) * p ^ (j.val + 1) := by
        rw [← pow_add]
        congr 1
        omega
  inj' := by
    letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
    intro g₁ g₂ hg
    apply Subtype.ext
    funext j
    apply ZMod.val_injective (p ^ k)
    have hquot := congrFun hg j
    have hq := congrArg Fin.val hquot
    change (g₁.1 j).val / (p ^ (j.val + 1)) =
      (g₂.1 j).val / (p ^ (j.val + 1)) at hq
    have hmod₁ := g₁.2 j
    have hmod₂ := g₂.2 j
    have hdecomp₁ := Nat.mod_add_div (g₁.1 j).val (p ^ (j.val + 1))
    have hdecomp₂ := Nat.mod_add_div (g₂.1 j).val (p ^ (j.val + 1))
    calc
      (g₁.1 j).val =
          (g₁.1 j).val % p ^ (j.val + 1) +
            p ^ (j.val + 1) * ((g₁.1 j).val / p ^ (j.val + 1)) := hdecomp₁.symm
      _ = (g₂.1 j).val % p ^ (j.val + 1) +
            p ^ (j.val + 1) * ((g₂.1 j).val / p ^ (j.val + 1)) := by
              rw [hmod₁, hmod₂, hq]
      _ = (g₂.1 j).val := hdecomp₂

theorem sum_vinogradov_lift_exponents (k : ℕ) :
    (∑ j : Fin k, (k - (j.val + 1))) = k * (k - 1) / 2 := by
  calc
    (∑ j : Fin k, (k - (j.val + 1))) =
        ∑ j : Fin k, (Fin.revPerm j).val := by rfl
    _ = ∑ j : Fin k, j.val := Equiv.sum_comp Fin.revPerm (fun j : Fin k => j.val)
    _ = ∑ j ∈ Finset.range k, j := Fin.sum_univ_eq_sum_range (fun j => j) k
    _ = k * (k - 1) / 2 := Finset.sum_range_id k

theorem card_vinogradovCompatibleSignature_le
    {p k : ℕ} [Fact p.Prime]
    (h : (j : Fin k) → Fin (p ^ (j.val + 1))) :
    Fintype.card (VinogradovCompatibleSignature p k h) ≤
      p ^ (k * (k - 1) / 2) := by
  refine (Fintype.card_le_of_embedding
    (vinogradovCompatibleSignatureQuotientEmbedding Fact.out h)).trans_eq ?_
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact sum_vinogradov_lift_exponents k

/-- A `k`-tuple of residues modulo `p^k`, distinct after reduction modulo
`p`. -/
def VinogradovLinnikTuple (p k : ℕ) :=
  {x : Fin k → ZMod (p ^ k) //
    Function.Injective fun i => ((x i).cast : ZMod p)}

noncomputable instance vinogradovLinnikTupleFinite
    (p k : ℕ) [Fact p.Prime] : Finite (VinogradovLinnikTuple p k) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance vinogradovLinnikTupleFintype
    (p k : ℕ) [Fact p.Prime] : Fintype (VinogradovLinnikTuple p k) :=
  Fintype.ofFinite _

/-- Full-modulus vector of the first `k` power sums. -/
def vinogradovFullPowerSignature {p k : ℕ} (x : VinogradovLinnikTuple p k) :
    Fin k → ZMod (p ^ k) :=
  fun j => ∑ i : Fin k, x.1 i ^ (j.val + 1)

/-- Linnik's simultaneous-congruence solution type.  Coordinate `j`
prescribes the `(j+1)`-st power sum modulo `p^(j+1)`. -/
def VinogradovLinnikSolution (p k : ℕ)
    (h : (j : Fin k) → Fin (p ^ (j.val + 1))) :=
  {x : VinogradovLinnikTuple p k //
    ∀ j : Fin k,
      (vinogradovFullPowerSignature x j).val % (p ^ (j.val + 1)) = (h j).val}

noncomputable instance vinogradovLinnikSolutionFinite
    (p k : ℕ) [Fact p.Prime]
    (h : (j : Fin k) → Fin (p ^ (j.val + 1))) :
    Finite (VinogradovLinnikSolution p k h) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance vinogradovLinnikSolutionFintype
    (p k : ℕ) [Fact p.Prime]
    (h : (j : Fin k) → Fin (p ^ (j.val + 1))) :
    Fintype (VinogradovLinnikSolution p k h) := Fintype.ofFinite _

/-- Map a simultaneous-congruence solution to its chosen lifts of all power
sums modulo `p^k`. -/
def vinogradovLinnikSignatureMap {p k : ℕ}
    {h : (j : Fin k) → Fin (p ^ (j.val + 1))} :
    VinogradovLinnikSolution p k h → VinogradovCompatibleSignature p k h :=
  fun x => ⟨vinogradovFullPowerSignature x.1, x.2⟩

noncomputable instance vinogradovLinnikSignatureFiberFintype
    {p k : ℕ} [Fact p.Prime]
    {h : (j : Fin k) → Fin (p ^ (j.val + 1))}
    (g : VinogradovCompatibleSignature p k h) :
    Fintype {x : VinogradovLinnikSolution p k h //
      vinogradovLinnikSignatureMap x = g} := Fintype.ofFinite _

/-- Two solutions in one full-signature fibre differ only by a permutation. -/
theorem vinogradovLinnikSolution_multiset_eq_of_signature_eq
    {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    {h : (j : Fin k) → Fin (p ^ (j.val + 1))}
    (x y : VinogradovLinnikSolution p k h)
    (hsig : vinogradovLinnikSignatureMap x =
      vinogradovLinnikSignatureMap y) :
    Finset.univ.val.map x.1.1 = Finset.univ.val.map y.1.1 := by
  apply zmod_multiset_eq_of_powerSums_eq Fact.out hkp x.1.1 y.1.1 x.1.2 y.1.2
  intro j hjpos hjk
  let q : Fin k := ⟨j - 1, by omega⟩
  have hcoord := congrFun (congrArg Subtype.val hsig) q
  have hj : j - 1 + 1 = j := by omega
  simpa [vinogradovLinnikSignatureMap, vinogradovFullPowerSignature, q, hj] using hcoord

/-- Every fibre of Linnik's full-signature map contains at most `k!`
tuples. -/
theorem card_vinogradovLinnikSignatureFiber_le
    {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    {h : (j : Fin k) → Fin (p ^ (j.val + 1))}
    (g : VinogradovCompatibleSignature p k h) :
    Fintype.card {x : VinogradovLinnikSolution p k h //
      vinogradovLinnikSignatureMap x = g} ≤ k.factorial := by
  let Fiber := {x : VinogradovLinnikSolution p k h //
    vinogradovLinnikSignatureMap x = g}
  by_cases hne : Nonempty Fiber
  · let rep : Fiber := Classical.choice hne
    let embed : Fiber ↪
        {l : List (ZMod (p ^ k)) //
          l ∈ (List.ofFn rep.1.1.1).permutations} :=
      { toFun := fun x =>
          ⟨List.ofFn x.1.1.1, List.mem_permutations.mpr <|
            Multiset.coe_eq_coe.mp <| by
              simpa using
                (vinogradovLinnikSolution_multiset_eq_of_signature_eq hkp
                  x.1 rep.1 (x.2.trans rep.2.symm))⟩
        inj' := by
          intro x y hxy
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          apply List.ofFn_injective
          exact congrArg Subtype.val hxy }
    exact (Fintype.card_le_of_embedding embed).trans
      (card_permutation_list_subtype_le_factorial rep.1.1.1)
  · letI : IsEmpty Fiber := not_nonempty_iff.mp hne
    simp [Fiber, Fintype.card_eq_zero]

/-- **Linnik lifting bound.**  The number of distinct-mod-`p` tuples
solving the nested power-sum congruences is at most
`k! * p^(k(k-1)/2)`. -/
theorem card_vinogradovLinnikSolution_le
    {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (h : (j : Fin k) → Fin (p ^ (j.val + 1))) :
    Fintype.card (VinogradovLinnikSolution p k h) ≤
      k.factorial * p ^ (k * (k - 1) / 2) := by
  have hdecomp :
      Fintype.card (VinogradovLinnikSolution p k h) =
        ∑ g : VinogradovCompatibleSignature p k h,
          Fintype.card {x : VinogradovLinnikSolution p k h //
            vinogradovLinnikSignatureMap x = g} := by
    rw [← Fintype.card_sigma]
    exact (Fintype.card_congr
      (Equiv.sigmaFiberEquiv vinogradovLinnikSignatureMap)).symm
  rw [hdecomp]
  calc
    (∑ g : VinogradovCompatibleSignature p k h,
        Fintype.card {x : VinogradovLinnikSolution p k h //
          vinogradovLinnikSignatureMap x = g}) ≤
        ∑ _g : VinogradovCompatibleSignature p k h, k.factorial := by
          exact Finset.sum_le_sum fun g _ =>
            card_vinogradovLinnikSignatureFiber_le hkp g
    _ = Fintype.card (VinogradovCompatibleSignature p k h) * k.factorial := by simp
    _ ≤ p ^ (k * (k - 1) / 2) * k.factorial :=
      Nat.mul_le_mul_right k.factorial (card_vinogradovCompatibleSignature_le h)
    _ = k.factorial * p ^ (k * (k - 1) / 2) := Nat.mul_comm _ _

end


end RHTower.Sieve
