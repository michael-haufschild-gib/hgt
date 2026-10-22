import GaloisForLFunctions.RHTower.Sieve.VinogradovResidueGoodCount
import GaloisForLFunctions.RHTower.Sieve.FinitePowerSumHolder
import GaloisForLFunctions.RHTower.Sieve.VinogradovCollisionRecurrence

/-!
# Energy of separated leading blocks in the Vinogradov recurrence

Bounds the part of the power-sum fibre energy of `(k + b)`-tuples in which the leading `k`-block has
entries distinct modulo the prime `p`. The energy is rewritten as a lead-tail signature energy, a
Hölder-type inequality over the residue classes of the tail entries costs a factor `p^(2b-1)`, and
each residue class is bounded by the good-completion count. The result is
`E_sep ≤ p^(2b) · N^k · k! p^(k(k-1)/2) · J_{b,k}(⌈N/p⌉)`.

## Main results

- `finiteFiberEnergyWith_eq_subtypeEnergy`: a restricted fibre energy equals the fibre energy of the
  restriction to the subtype.
- `finiteFiberEnergy_comp_equiv`: fibre energy is invariant under reparametrising the domain.
- `finiteFiberEnergyWith_separated_eq`: the separated-block energy equals a lead-tail signature energy.
- `finiteFiberEnergy_residueClass_eq_goodCompletion`: for a fixed residue class of the tail, this
  energy counts the good completions.
- `finiteFiberEnergyWith_separated_le`: the separated-block energy is at most
  `p^(2b) · N^k · k! p^(k(k-1)/2) · J_{b,k}(⌈N/p⌉)`.

## Hypotheses

Unconditional. The final bound assumes `b ≠ 0`, `p` prime, `k < p`, `N < p^k`, `N ≠ 0`,
`⌈N/p⌉ ≠ 0`, `2 (k + b) N^k < q`, `2 b ⌈N/p⌉^k < q`, and that `p` is a unit modulo `q`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The fibre energy of `f` restricted to `{a | P a}` equals the fibre energy of `f` on the subtype. -/
theorem finiteFiberEnergyWith_eq_subtypeEnergy
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (p : α → Prop) [DecidablePred p] :
    finiteFiberEnergyWith f p =
      finiteFiberEnergy (fun a : {a : α // p a} => f a.1) := by
  rw [finiteFiberEnergyWith_eq_card, finiteFiberEnergy_eq_card]
  let e : {z : α × α // p z.1 ∧ p z.2 ∧ f z.1 = f z.2} ≃
      {z : {a : α // p a} × {a : α // p a} // f z.1.1 = f z.2.1} :=
    { toFun := fun z => ⟨(⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2.1⟩), z.2.2.2⟩
      invFun := fun z => ⟨(z.1.1.1, z.1.2.1),
        ⟨z.1.1.2, z.1.2.2, z.2⟩⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun z => Subtype.ext rfl }
  exact Fintype.card_congr e

/-- Fibre energy is unchanged by precomposing with an equivalence of the domain. -/
theorem finiteFiberEnergy_comp_equiv
    {α γ β : Type*} [Fintype α] [Fintype γ] [Fintype β]
    [DecidableEq β] (e : α ≃ γ) (f : γ → β) :
    finiteFiberEnergy (f ∘ e) = finiteFiberEnergy f := by
  rw [finiteFiberEnergy_eq_card, finiteFiberEnergy_eq_card]
  let E : {z : α × α // (f ∘ e) z.1 = (f ∘ e) z.2} ≃
      {z : γ × γ // f z.1 = f z.2} :=
    { toFun := fun z => ⟨(e z.1.1, e z.1.2), z.2⟩
      invFun := fun z => ⟨(e.symm z.1.1, e.symm z.1.2), by
        change f (e (e.symm z.1.1)) = f (e (e.symm z.1.2))
        simpa using z.2⟩
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun z => Subtype.ext (by simp) }
  exact Fintype.card_congr E

/-- Power vector `(n, n^2, ..., n^k)` modulo `q` of one entry `n ∈ [0, N)`. -/
def vinogradovPowerAtom (q k N : ℕ) (n : Fin N) : Fin k → ZMod q :=
  fun j => ((n.val : ZMod q) ^ (j.val + 1))

/-- The power-sum signature of a tuple is the sum of the power vectors of its entries. -/
theorem vinogradovPowerSignatureMod_eq_sum_atom
    {q N k b : ℕ} (u : Fin b → Fin N) :
    vinogradovPowerSignatureMod q k u =
      ∑ i : Fin b, vinogradovPowerAtom q k N (u i) := by
  funext j
  simp [vinogradovPowerSignatureMod, vinogradovPowerAtom]

theorem finiteLeadTailSignature_vinogradov
    {q N p k b : ℕ} [NeZero q] :
    finiteLeadTailSignature q k b
        (fun x : VinogradovInjectiveBlock N p k =>
          vinogradovPowerSignatureMod q k x.1)
        (vinogradovPowerAtom q k N) =
      fun z => vinogradovPowerSignatureMod q k (Fin.append z.1.1 z.2) := by
  funext z j
  simp [finiteLeadTailSignature, vinogradovPowerSignatureMod,
    vinogradovPowerAtom, Fin.sum_univ_add]

/-- A tuple whose entries are distinct modulo `p` has distinct entries. -/
theorem injective_of_injective_mod
    {N p k : ℕ} {x : Fin k → Fin N}
    (hx : Function.Injective fun i => ((x i).val : ZMod p)) :
    Function.Injective x := by
  intro i j hij
  apply hx
  exact congrArg (fun n : Fin N => (n.val : ZMod p)) hij

/-- Pairs (block, tail) whose block is injective and injective modulo `p` are equivalent to pairs of
an injective-mod-`p` block and an arbitrary tail. -/
def vinogradovSeparatedSplitEquiv (N p k b : ℕ) :
    {z : (Fin k → Fin N) × (Fin b → Fin N) //
      Function.Injective z.1 ∧
        Function.Injective (fun i => ((z.1 i).val : ZMod p))} ≃
      VinogradovInjectiveBlock N p k × (Fin b → Fin N) where
  toFun z := (⟨z.1.1, z.2.2⟩, z.1.2)
  invFun z := ⟨(z.1.1, z.2), injective_of_injective_mod z.1.2, z.1.2⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => rfl

/-- The split-signature energy restricted to leading blocks injective modulo `p` equals the energy of
the lead-tail signature on (injective-mod-`p` block, tail) pairs. -/
theorem finiteFiberEnergyWith_separated_eq
    {q N p k b : ℕ} [NeZero q] :
    finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
        (fun z => Function.Injective z.1 ∧
          Function.Injective (fun i => ((z.1 i).val : ZMod p))) =
      finiteFiberEnergy (finiteLeadTailSignature q k b
        (fun x : VinogradovInjectiveBlock N p k =>
          vinogradovPowerSignatureMod q k x.1)
        (vinogradovPowerAtom q k N)) := by
  rw [finiteFiberEnergyWith_eq_subtypeEnergy]
  let e := vinogradovSeparatedSplitEquiv N p k b
  have hcomp :
      (fun z : {z : (Fin k → Fin N) × (Fin b → Fin N) //
          Function.Injective z.1 ∧
            Function.Injective (fun i => ((z.1 i).val : ZMod p))} =>
        vinogradovSplitPowerSignature q N k b z.1) =
        (finiteLeadTailSignature q k b
          (fun x : VinogradovInjectiveBlock N p k =>
            vinogradovPowerSignatureMod q k x.1)
          (vinogradovPowerAtom q k N)) ∘ e := by
    funext z
    rw [finiteLeadTailSignature_vinogradov]
    simp [e, vinogradovSeparatedSplitEquiv, vinogradovSplitPowerSignature,
      Function.comp_apply]
  rw [hcomp, finiteFiberEnergy_comp_equiv]

/-- With tails restricted to the residue class `a` modulo `p`, the lead-tail signature energy equals
the number of good completions `VinogradovResidueGoodCompletion q N p k b a`. -/
theorem finiteFiberEnergy_residueClass_eq_goodCompletion
    {q N p k b : ℕ} [NeZero q] [NeZero p] (a : ZMod p) :
    finiteFiberEnergy (finiteLeadTailSignature q k b
        (fun x : VinogradovInjectiveBlock N p k =>
          vinogradovPowerSignatureMod q k x.1)
        (fun n : {n : Fin N // ((n.val : ZMod p) = a)} =>
          vinogradovPowerAtom q k N n.1)) =
      Fintype.card (VinogradovResidueGoodCompletion q N p k b a) := by
  have hsignature :
      finiteLeadTailSignature q k b
          (fun x : VinogradovInjectiveBlock N p k =>
            vinogradovPowerSignatureMod q k x.1)
          (fun n : {n : Fin N // ((n.val : ZMod p) = a)} =>
            vinogradovPowerAtom q k N n.1) =
        fun z => vinogradovPowerSignatureMod q k
          (Fin.append z.1.1 (fun i => (z.2 i).1)) := by
    funext z j
    simp [finiteLeadTailSignature, vinogradovPowerSignatureMod,
      vinogradovPowerAtom, Fin.sum_univ_add]
  rw [finiteFiberEnergy_eq_card]
  let e : {z :
        (VinogradovInjectiveBlock N p k ×
          (Fin b → {n : Fin N // ((n.val : ZMod p) = a)})) ×
        (VinogradovInjectiveBlock N p k ×
          (Fin b → {n : Fin N // ((n.val : ZMod p) = a)})) //
      finiteLeadTailSignature q k b
          (fun x : VinogradovInjectiveBlock N p k =>
            vinogradovPowerSignatureMod q k x.1)
          (fun n : {n : Fin N // ((n.val : ZMod p) = a)} =>
            vinogradovPowerAtom q k N n.1) z.1 =
        finiteLeadTailSignature q k b
          (fun x : VinogradovInjectiveBlock N p k =>
            vinogradovPowerSignatureMod q k x.1)
          (fun n : {n : Fin N // ((n.val : ZMod p) = a)} =>
            vinogradovPowerAtom q k N n.1) z.2} ≃
      VinogradovResidueGoodCompletion q N p k b a :=
    { toFun := fun z => ⟨z.1, by
        simpa only [hsignature] using z.2⟩
      invFun := fun z => ⟨z.1, by
        simpa only [hsignature] using z.2⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun z => Subtype.ext rfl }
  exact Fintype.card_congr e

/-- Under `b ≠ 0`, `p` prime, `k < p`, `N < p^k`, `N, ⌈N/p⌉ ≠ 0`, `p` a unit modulo `q` and
`2 (k + b) N^k, 2 b ⌈N/p⌉^k < q`: the separated-block energy is at most
`p^(2b) · N^k · k! p^(k(k-1)/2) · J_{b,k}(⌈N/p⌉)`. -/
theorem finiteFiberEnergyWith_separated_le
    {q N p k b : ℕ} [NeZero q] [NeZero p]
    (hb : b ≠ 0) (hp : p.Prime) (hkp : k < p) (hNp : N < p ^ k)
    (hN : N ≠ 0) (hqfull : 2 * (k + b) * N ^ k < q)
    (hpunit : IsUnit (p : ZMod q))
    (hM : N ⌈/⌉ p ≠ 0) (hqtail : 2 * b * (N ⌈/⌉ p) ^ k < q) :
    finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
        (fun z => Function.Injective z.1 ∧
          Function.Injective (fun i => ((z.1 i).val : ZMod p))) ≤
      p ^ (2 * b) *
        (N ^ k * (k.factorial * p ^ (k * (k - 1) / 2) *
          Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ p) b k))) := by
  classical
  let C := N ^ k * (k.factorial * p ^ (k * (k - 1) / 2) *
    Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ p) b k))
  calc
    finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
        (fun z => Function.Injective z.1 ∧
          Function.Injective (fun i => ((z.1 i).val : ZMod p))) =
        finiteFiberEnergy (finiteLeadTailSignature q k b
          (fun x : VinogradovInjectiveBlock N p k =>
            vinogradovPowerSignatureMod q k x.1)
          (vinogradovPowerAtom q k N)) :=
      finiteFiberEnergyWith_separated_eq
    _ ≤ p ^ (2 * b - 1) *
        ∑ a : ZMod p, finiteFiberEnergy (finiteLeadTailSignature q k b
          (fun x : VinogradovInjectiveBlock N p k =>
            vinogradovPowerSignatureMod q k x.1)
          (fun n : {n : Fin N // ((n.val : ZMod p) = a)} =>
            vinogradovPowerAtom q k N n.1)) := by
      simpa using finiteFiberEnergy_le_residueClasses
        (L := VinogradovInjectiveBlock N p k) (A := Fin N) (ι := ZMod p)
        q k b hb
        (fun x => vinogradovPowerSignatureMod q k x.1)
        (vinogradovPowerAtom q k N)
        (fun n => (n.val : ZMod p))
    _ ≤ p ^ (2 * b - 1) * ∑ _a : ZMod p, C := by
      gcongr
      rw [finiteFiberEnergy_residueClass_eq_goodCompletion]
      exact card_vinogradovResidueGoodCompletion_le
        hp hkp hNp hN hqfull hpunit a hM hqtail
    _ = p ^ (2 * b) * C := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card]
      simp only [nsmul_eq_mul]
      change p ^ (2 * b - 1) * (p * C) = p ^ (2 * b) * C
      rw [← mul_assoc, ← Nat.pow_succ]
      congr 2
      omega

end

end RHTower.Sieve
