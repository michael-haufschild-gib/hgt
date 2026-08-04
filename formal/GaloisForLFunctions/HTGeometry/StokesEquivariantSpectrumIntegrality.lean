import GaloisForLFunctions.HTGeometry.StokesFinitePuiseuxDendrogram
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

open scoped BigOperators

namespace GaloisForLFunctions.IrregularStokes

noncomputable section

namespace Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Number of points in the cyclic orbit of `x`, including singleton fixed orbits. -/
def orbitCard (p : Equiv.Perm α) (x : α) : ℕ :=
  Fintype.card {y // p.SameCycle x y}

theorem orbitCard_eq_one_of_fixed (p : Equiv.Perm α) {x : α} (hx : p x = x) :
    orbitCard p x = 1 := by
  rw [orbitCard, Fintype.card_eq_one_iff]
  exact ⟨⟨x, .rfl⟩, fun y ↦ Subtype.ext ((y.prop.eq_of_left hx).symm)⟩

theorem orbitCard_eq_support_cycleOf (p : Equiv.Perm α) {x : α} (hx : p x ≠ x) :
    orbitCard p x = (p.cycleOf x).support.card := by
  rw [orbitCard, Fintype.card_subtype]
  congr 1
  ext y
  simpa [Equiv.Perm.mem_support_cycleOf_iff' hx]

theorem pow_orbitCard_apply (p : Equiv.Perm α) (x : α) :
    (p ^ orbitCard p x) x = x := by
  by_cases hx : p x = x
  · rw [orbitCard_eq_one_of_fixed p hx]
    simpa using hx
  · rw [orbitCard_eq_support_cycleOf p hx]
    have hcycle : (p.cycleOf x) ^ (p.cycleOf x).support.card = 1 := by
      rw [← (Equiv.Perm.isCycle_cycleOf p hx).orderOf]
      exact pow_orderOf_eq_one _
    have happ := DFunLike.congr_fun hcycle x
    rw [Equiv.Perm.cycleOf_pow_apply_self] at happ
    exact happ

theorem orbitCard_pos (p : Equiv.Perm α) (x : α) : 0 < orbitCard p x := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨x, .rfl⟩⟩

/-- An orbitwise-constant natural weight has a globally divisible sum as soon as every cyclic
orbit contribution is divisible. -/
theorem dvd_sum_of_dvd_orbitCard_mul (p : Equiv.Perm α) (N : ℕ) (w : α → ℕ)
    (hinv : ∀ x, w (p x) = w x)
    (horbit : ∀ x, N ∣ orbitCard p x * w x) :
    N ∣ ∑ x, w x := by
  classical
  let q : α → Quotient (Equiv.Perm.SameCycle.setoid p) :=
    fun x => Quotient.mk (Equiv.Perm.SameCycle.setoid p) x
  rw [← Finset.sum_fiberwise Finset.univ q w]
  apply Finset.dvd_sum
  intro c _
  induction c using Quotient.inductionOn with
  | _ x =>
      have hpow : ∀ n z, w ((p ^ n) z) = w z := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            intro z
            rw [pow_succ', Equiv.Perm.mul_apply, hinv, ih]
      have hconst : ∀ y ∈ Finset.univ.filter (fun y => q y = q x), w y = w x := by
        intro y hy
        have hsame : p.SameCycle x y := by
          exact (Quotient.exact (Finset.mem_filter.mp hy).2.symm)
        obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
        rw [← hn]
        exact hpow n x
      rw [Finset.sum_const_nat hconst]
      have hcard : (Finset.univ.filter fun y => q y = q x).card = orbitCard p x := by
        rw [orbitCard, Fintype.card_subtype]
        congr 1
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change (q y = q x) ↔ p.SameCycle x y
        constructor
        · intro h
          exact (Quotient.exact h).symm
        · intro h
          exact Quotient.sound h.symm
      rw [hcard]
      exact horbit x

end Equiv.Perm

namespace FinitePuiseuxFamily

variable {m K N : ℕ}

/-- At the highest positive contact of distinct branches, their coefficients actually differ. -/
theorem coeff_ne_at_contact (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) :
    p.coeff i ⟨p.contactNumerator i j, Nat.lt_succ_of_le (p.contactNumerator_le i j)⟩ ≠
      p.coeff j ⟨p.contactNumerator i j,
        Nat.lt_succ_of_le (p.contactNumerator_le i j)⟩ := by
  let f : Fin (K + 1) → ℕ :=
    fun e => if p.coeff i e = p.coeff j e then 0 else e.val
  obtain ⟨e, -, he⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty f
  have hcontact : p.contactNumerator i j = f e := by
    simpa [FinitePuiseuxFamily.contactNumerator, f] using he
  have hpos := p.contactNumerator_pos_of_ne hij
  have hcoeff : p.coeff i e ≠ p.coeff j e := by
    intro h
    simp [f, h] at hcontact
    omega
  have heval : e.val = p.contactNumerator i j := by
    simpa [f, hcoeff] using hcontact.symm
  have heq : e = ⟨p.contactNumerator i j,
      Nat.lt_succ_of_le (p.contactNumerator_le i j)⟩ := Fin.ext heval
  simpa [heq] using hcoeff

end FinitePuiseuxFamily

/-- Finite Puiseux coefficients equipped with genuine cyclic Galois equivariance. -/
structure EquivariantFinitePuiseuxFamily (m K N : ℕ)
    extends FinitePuiseuxFamily m K N where
  monodromy : Equiv.Perm (Fin m)
  monodromy_pow : monodromy ^ N = 1
  root : ℂ
  root_primitive : IsPrimitiveRoot root N
  coeff_equivariant : ∀ i e,
    coeff (monodromy i) e = (root⁻¹ ^ e.val) * coeff i e

namespace EquivariantFinitePuiseuxFamily

variable {m K N : ℕ}

theorem root_ne_zero (p : EquivariantFinitePuiseuxFamily m K N) : p.root ≠ 0 :=
  p.root_primitive.ne_zero (Nat.ne_of_gt p.coverDegree_pos)

/-- Coefficient equivariance iterated through any number of monodromy turns. -/
theorem coeff_iterate (p : EquivariantFinitePuiseuxFamily m K N)
    (n : ℕ) (i : Fin m) (e : Fin (K + 1)) :
    p.coeff ((p.monodromy ^ n) i) e =
      (p.root⁻¹ ^ e.val) ^ n * p.coeff i e := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, p.coeff_equivariant, ih]
      ring

/-- Highest-difference contact is constant under simultaneous analytic continuation. -/
theorem contactNumerator_monodromy (p : EquivariantFinitePuiseuxFamily m K N)
    (i j : Fin m) :
    p.contactNumerator (p.monodromy i) (p.monodromy j) = p.contactNumerator i j := by
  apply Finset.sup_congr rfl
  intro e _
  have hs : p.root⁻¹ ^ e.val ≠ 0 := pow_ne_zero _ (inv_ne_zero p.root_ne_zero)
  have heq : p.coeff (p.monodromy i) e = p.coeff (p.monodromy j) e ↔
      p.coeff i e = p.coeff j e := by
    rw [p.coeff_equivariant, p.coeff_equivariant]
    exact ⟨mul_left_cancel₀ hs, congrArg _⟩
  simp only [FinitePuiseuxFamily.contactNumerator]
  rw [if_congr heq rfl rfl]

/-- Monodromy orbit through one exponential label. -/
abbrev Orbit (p : EquivariantFinitePuiseuxFamily m K N) (a : Fin m) :=
  {x // p.monodromy.SameCycle a x}

/-- Monodromy restricted to one cyclic orbit. -/
def orbitPerm (p : EquivariantFinitePuiseuxFamily m K N) (a : Fin m) :
    Equiv.Perm (p.Orbit a) :=
  p.monodromy.subtypePerm fun _ => Equiv.Perm.sameCycle_apply_right

/-- Simultaneous monodromy on a product of two Galois orbits. -/
def pairOrbitPerm (p : EquivariantFinitePuiseuxFamily m K N) (a b : Fin m) :
    Equiv.Perm (p.Orbit a × p.Orbit b) :=
  Equiv.prodCongr (p.orbitPerm a) (p.orbitPerm b)

@[simp] theorem orbitPerm_apply_val (p : EquivariantFinitePuiseuxFamily m K N)
    (a : Fin m) (x : p.Orbit a) :
    (p.orbitPerm a x).val = p.monodromy x.val := rfl

@[simp] theorem pairOrbitPerm_apply_fst_val (p : EquivariantFinitePuiseuxFamily m K N)
    (a b : Fin m) (x : p.Orbit a × p.Orbit b) :
    (p.pairOrbitPerm a b x).1.val = p.monodromy x.1.val := rfl

@[simp] theorem pairOrbitPerm_apply_snd_val (p : EquivariantFinitePuiseuxFamily m K N)
    (a b : Fin m) (x : p.Orbit a × p.Orbit b) :
    (p.pairOrbitPerm a b x).2.val = p.monodromy x.2.val := rfl

theorem pairOrbitPerm_pow_fst_val (p : EquivariantFinitePuiseuxFamily m K N)
    (a b : Fin m) (n : ℕ) (x : p.Orbit a × p.Orbit b) :
    ((p.pairOrbitPerm a b ^ n) x).1.val = (p.monodromy ^ n) x.1.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        pairOrbitPerm_apply_fst_val, ih]

theorem pairOrbitPerm_pow_snd_val (p : EquivariantFinitePuiseuxFamily m K N)
    (a b : Fin m) (n : ℕ) (x : p.Orbit a × p.Orbit b) :
    ((p.pairOrbitPerm a b ^ n) x).2.val = (p.monodromy ^ n) x.2.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        pairOrbitPerm_apply_snd_val, ih]

/-- Every simultaneous pair orbit contributes an integer after division by the cover degree.
This is the primitive-root stabilizer argument at the actual highest differing coefficient. -/
theorem coverDegree_dvd_pairOrbitContribution
    (p : EquivariantFinitePuiseuxFamily m K N) (a b : Fin m)
    (x : p.Orbit a × p.Orbit b) :
    N ∣ Equiv.Perm.orbitCard (p.pairOrbitPerm a b) x *
      p.contactNumerator x.1.val x.2.val := by
  let L := Equiv.Perm.orbitCard (p.pairOrbitPerm a b) x
  by_cases hsame : x.1.val = x.2.val
  · simp [hsame]
  · let k := p.contactNumerator x.1.val x.2.val
    let e : Fin (K + 1) := ⟨k, Nat.lt_succ_of_le (p.contactNumerator_le _ _)⟩
    have hpairfix := Equiv.Perm.pow_orbitCard_apply (p.pairOrbitPerm a b) x
    have hfix1 : (p.monodromy ^ L) x.1.val = x.1.val := by
      rw [← p.pairOrbitPerm_pow_fst_val a b L x, hpairfix]
    have hfix2 : (p.monodromy ^ L) x.2.val = x.2.val := by
      rw [← p.pairOrbitPerm_pow_snd_val a b L x, hpairfix]
    have hdiff : p.coeff x.1.val e ≠ p.coeff x.2.val e := by
      simpa [e, k] using p.toFinitePuiseuxFamily.coeff_ne_at_contact hsame
    have hiter1 := p.coeff_iterate L x.1.val e
    have hiter2 := p.coeff_iterate L x.2.val e
    rw [hfix1] at hiter1
    rw [hfix2] at hiter2
    have hdifference : p.coeff x.1.val e - p.coeff x.2.val e ≠ 0 :=
      sub_ne_zero.mpr hdiff
    have hscalar : (p.root⁻¹ ^ e.val) ^ L = 1 := by
      apply mul_right_cancel₀ hdifference
      calc
        (p.root⁻¹ ^ e.val) ^ L *
              (p.coeff x.1.val e - p.coeff x.2.val e) =
            (p.root⁻¹ ^ e.val) ^ L * p.coeff x.1.val e -
              (p.root⁻¹ ^ e.val) ^ L * p.coeff x.2.val e := by ring
        _ = p.coeff x.1.val e - p.coeff x.2.val e := by rw [← hiter1, ← hiter2]
        _ = 1 * (p.coeff x.1.val e - p.coeff x.2.val e) := by simp
    have hinvpow : (p.root⁻¹) ^ (e.val * L) = 1 := by
      simpa [pow_mul] using hscalar
    have hrootpow : p.root ^ (e.val * L) = 1 := by
      have h := congrArg Inv.inv hinvpow
      simpa [inv_pow] using h
    have hdvd : N ∣ e.val * L :=
      (p.root_primitive.pow_eq_one_iff_dvd (e.val * L)).mp hrootpow
    simpa [L, k, e, Nat.mul_comm] using hdvd

/-- Exact sum of contact numerators over two full Galois orbits. -/
def orbitContactNumeratorSum (p : EquivariantFinitePuiseuxFamily m K N) (a b : Fin m) : ℕ :=
  ∑ x : p.Orbit a, ∑ y : p.Orbit b, p.contactNumerator x.val y.val

/-- Arbitrary equivariant finite-spectrum Galois integrality: the full pair-orbit numerator sum
is divisible by the ramified cover degree. -/
theorem coverDegree_dvd_orbitContactNumeratorSum
    (p : EquivariantFinitePuiseuxFamily m K N) (a b : Fin m) :
    N ∣ p.orbitContactNumeratorSum a b := by
  let pairWeight : p.Orbit a × p.Orbit b → ℕ :=
    fun x => p.contactNumerator x.1.val x.2.val
  have hinv : ∀ x, pairWeight (p.pairOrbitPerm a b x) = pairWeight x := by
    intro x
    exact p.contactNumerator_monodromy x.1.val x.2.val
  have horbit : ∀ x, N ∣ Equiv.Perm.orbitCard (p.pairOrbitPerm a b) x * pairWeight x :=
    p.coverDegree_dvd_pairOrbitContribution a b
  have h := Equiv.Perm.dvd_sum_of_dvd_orbitCard_mul
    (p.pairOrbitPerm a b) N pairWeight hinv horbit
  simpa [orbitContactNumeratorSum, pairWeight, Fintype.sum_prod_type] using h

/-- Descended integral contact attached to a pair of monodromy orbits. -/
def orbitContactIndex (p : EquivariantFinitePuiseuxFamily m K N) (a b : Fin m) : ℕ :=
  p.orbitContactNumeratorSum a b / N

/-- The descended contact index is exact: multiplying by `N` recovers the entire sheet-pair
highest-difference mass. -/
theorem coverDegree_mul_orbitContactIndex
    (p : EquivariantFinitePuiseuxFamily m K N) (a b : Fin m) :
    N * p.orbitContactIndex a b = p.orbitContactNumeratorSum a b := by
  exact Nat.mul_div_cancel' (p.coverDegree_dvd_orbitContactNumeratorSum a b)

end EquivariantFinitePuiseuxFamily

end

end GaloisForLFunctions.IrregularStokes
