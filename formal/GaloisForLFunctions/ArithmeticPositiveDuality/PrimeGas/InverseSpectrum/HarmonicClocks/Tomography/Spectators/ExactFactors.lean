import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HeatTrace
import GaloisForLFunctions.RHTower.ThetaEulerTwoPortJetPole

/-! # Finite-prime restrictions of exact arithmetic tensor factors -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

variable {ι κ : Type*}

/-- The independent subsystems have exactly one product state at each arithmetic label. -/
def exactLabelProduct (a : ι → ℕ+) (b : κ → ℕ+) : Prop :=
  Function.Bijective (fun u : ι × κ => a u.1 * b u.2)

/-- States whose total label uses only the primes in a finite window. -/
abbrev WindowState (P : Finset ℕ) (a : ι → ℕ+) := {i : ι // (a i).val ∈ Nat.factoredNumbers P}

def windowTrace (P : Finset ℕ) (a : ι → ℕ+) (s : ℂ) := ∑' i : WindowState P a, heat s (a i.val)

private theorem local_label_injective {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    Function.Injective a ∧ Function.Injective b := by
  obtain ⟨v,_⟩ := h.2 1
  constructor
  · intro i j he
    exact congrArg Prod.fst (h.1 (a₁ := (i,v.2)) (a₂ := (j,v.2)) (congrArg (· * b v.2) he))
  · intro i j he
    exact congrArg Prod.snd (h.1 (a₁ := (v.1,i)) (a₂ := (v.1,j)) (congrArg (a v.1 * ·) he))

/-- Product label of a pair of subsystem states supported in the same prime window. -/
def windowProduct (P : Finset ℕ) (a : ι → ℕ+) (b : κ → ℕ+)
    (u : WindowState P a × WindowState P b) : Nat.factoredNumbers P :=
  ⟨(a u.1.val).val * (b u.2.val).val,Nat.mul_mem_factoredNumbers u.1.property u.2.property⟩

/-- Restriction to finitely many prime species preserves the exact product of the state spaces. -/
theorem windowProduct_bijective (P : Finset ℕ) {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    Function.Bijective (windowProduct P a b) := by
  constructor
  · intro u v he
    have hh := h.1 (a₁ := (u.1.val,u.2.val)) (a₂ := (v.1.val,v.2.val))
      (PNat.coe_injective (congrArg (fun n : Nat.factoredNumbers P => n.val) he))
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  · intro n
    obtain ⟨⟨i,j⟩,he⟩ := h.2 ⟨n.val,Nat.pos_of_ne_zero (Nat.mem_factoredNumbers.mp n.property).1⟩
    have hv : (a i).val*(b j).val = n.val := congrArg PNat.val he
    have hm : (a i).val*(b j).val ∈ Nat.factoredNumbers P := hv ▸ n.property
    exact ⟨(⟨i,Nat.mem_factoredNumbers_of_dvd hm (dvd_mul_right _ _)⟩,
      ⟨j,Nat.mem_factoredNumbers_of_dvd hm (dvd_mul_left _ _)⟩),Subtype.ext hv⟩

private theorem window_summable (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {s : ℂ} (hs : 0 < s.re)
    (a : ι → ℕ+) (ha : Function.Injective a) : Summable (fun i : WindowState P a => ‖heat s (a i.val)‖) := by
  let j (i : WindowState P a) : Nat.factoredNumbers P := ⟨(a i.val).val,i.property⟩
  have hj : Function.Injective j := fun _ _ he =>
    Subtype.ext (ha (PNat.coe_injective (congrArg (fun n : Nat.factoredNumbers P => n.val) he)))
  simpa only [heat_eq_cpow,Function.comp_def,j] using
    (_root_.RHTower.hasSum_factoredNumbers_cpow P hP hs).1.comp_injective hj

/-- Both subsystem traces converge absolutely on the full positive half-plane in each window. -/
theorem exactWindow_absolute (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun i : WindowState P a => ‖heat s (a i.val)‖) ∧
      Summable (fun j : WindowState P b => ‖heat s (b j.val)‖) :=
  ⟨window_summable P hP hs a (local_label_injective h).1,window_summable P hP hs b (local_label_injective h).2⟩

/-- Reindexing all smooth labels recovers the entire finite Euler product. -/
theorem exactWindow_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) {s : ℂ} (hs : 0 < s.re) :
    windowTrace P a s * windowTrace P b s = _root_.RHTower.thetaEulerStageZeta P s := by
  let e := Equiv.ofBijective (windowProduct P a b) (windowProduct_bijective P h)
  have hsum : HasSum (fun u : WindowState P a × WindowState P b => heat s (a u.1.val) * heat s (b u.2.val))
      (_root_.RHTower.thetaEulerStageZeta P s) := by
    have hbase := (_root_.RHTower.hasSum_factoredNumbers_cpow P hP hs).2
    have he := (e.hasSum_iff (f := fun n : Nat.factoredNumbers P => (n.val:ℂ)^(-s))).mpr hbase
    apply he.congr_fun
    intro u
    exact (heat_mul s _ _).symm.trans (heat_eq_cpow s _)
  rw [← hsum.tsum_eq,hsum.summable.tsum_prod]
  simp only [windowTrace,tsum_mul_left,tsum_mul_right]

/-- A zero of a restricted trace excludes exact independent composition into the arithmetic gas. -/
theorem exactWindow_zero_free (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) {s : ℂ} (hs : 0 < s.re) : windowTrace P a s ≠ 0 ∧ windowTrace P b s ≠ 0 :=
  mul_ne_zero_iff.mp ((exactWindow_product P hP h hs).trans_ne (_root_.RHTower.thetaEulerStageZeta_ne_zero P hP hs))

/-- Every finite-state tensor factor of the exact gas has zero-free partition throughout Re(s)>0,
even when its complementary factor uses infinitely many prime species. -/
theorem finiteSubsystem_zero_free [Fintype ι] {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b)
    {s : ℂ} (hs : 0 < s.re) : (∑ i, heat s (a i)) ≠ 0 := by
  classical
  let P := Finset.univ.biUnion fun i => (a i).val.primeFactors
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors hi
  have hmem (i : ι) : (a i).val ∈ Nat.factoredNumbers P := by
    apply Nat.mem_factoredNumbers_of_primeFactors_subset (a i).ne_zero
    exact fun _ hp => Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hp⟩
  let e : WindowState P a ≃ ι := Equiv.subtypeUnivEquiv hmem
  have he : windowTrace P a s = ∑ i, heat s (a i) :=
    (e.tsum_eq (fun i => heat s (a i))).trans (tsum_fintype _)
  exact he ▸ (exactWindow_zero_free P hP h hs).1

#print axioms windowProduct_bijective
#print axioms exactWindow_absolute
#print axioms exactWindow_product
#print axioms exactWindow_zero_free
#print axioms finiteSubsystem_zero_free

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
