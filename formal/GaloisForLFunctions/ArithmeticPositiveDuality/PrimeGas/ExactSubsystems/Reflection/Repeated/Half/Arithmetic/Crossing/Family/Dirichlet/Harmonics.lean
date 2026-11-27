import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Closure

/-! # Separating integer harmonics and isolating logarithmic orders -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Real Finset Set

/-- Raising each integer shell to the kth power dilates all thermal tests at once. -/
theorem forces_dilate {t u : ℝ} (h : Forces t u) (k : ℕ) :
    Forces (t*k) (u*k) := by
  intro n a
  let b (i : Fin n) := a i ^ k
  have eq : energy ∘ b = fun i => (k : ℝ)*(energy ∘ a) i+0 := by
    funext i
    simp only [Function.comp_apply,b,energy,PNat.pow_coe,Nat.cast_pow,log_pow,add_zero]
  have f := h n b
  rwa [eq,agrees_affine,agrees_affine] at f

/-- No resonant positive order forces any proper integral harmonic. -/
theorem excludes_harmonic {t : ℝ} (ht : 0<t) (rt : Resonant t) (m : ℕ) (hm : 1 < m) :
    ¬Forces t (t*m) := by
  intro h
  have orbit (k : ℕ) : Forces t (t*(m : ℝ)^k) := by
    induction k with
    | zero => simpa only [pow_zero,mul_one] using (show Forces t t from fun _ _ hit => hit)
    | succ k ih =>
      have step := forces_dilate h (m^k)
      rw [Nat.cast_pow,show t*(m : ℝ)*(m : ℝ)^k=t*(m : ℝ)^(k+1) by ring] at step
      exact fun n a hit => step n a (ih n a hit)
  have finite := attainable_finite (least_spectrum ht rt)
  let f (k : ℕ) := t*(m : ℝ)^k
  have mono : StrictMono f := fun _ _ lt => mul_lt_mul_of_pos_left
    (pow_lt_pow_right₀ (Nat.one_lt_cast.mpr hm) lt) ht
  apply (Set.infinite_range_of_injective mono.injective).not_finite
  apply finite.subset
  rintro _ ⟨k,rfl⟩
  exact ⟨mul_pos ht (pow_pos (by exact_mod_cast (Nat.zero_lt_of_lt hm)) k),orbit k⟩

theorem separate_harmonics {t : ℝ} (ht : 0<t) (rt : Resonant t) :
    ∃ S, Attainable S ∧ t ∈ S ∧ ∀ m : ℕ, 1 < m → t*m ∉ S :=
  ⟨consequences t,least_spectrum ht rt,⟨ht,fun _ _ h => h⟩,
    fun m hm hit => excludes_harmonic ht rt m hm hit.2⟩

/-- A two-term polynomial detects a single positive ratio of rational log gaps. -/
theorem isolated_ratio (a b c d : ℕ+) (gap : energy a ≠ energy b)
    (pos : 0<(energy c-energy d)/(energy a-energy b)) :
    Attainable {(energy c-energy d)/(energy a-energy b)} := by
  let t := (energy c-energy d)/(energy a-energy b)
  let P : PolynomialRing := (d.val : PolynomialRing)*atom a-(c.val : PolynomialRing)*atom b
  have ex (n : ℕ+) : exp (energy n)=(n.val : ℝ) := exp_log (Nat.cast_pos.mpr n.pos)
  have root (s : ℝ) : value s P=0 ↔ s=t := by
    simp only [P,map_sub,map_mul,map_natCast,value_atom,sub_eq_zero]
    rw [← ex d,← ex c,← exp_add,← exp_add,Real.exp_injective.eq_iff]
    change _ ↔ s=(energy c-energy d)/(energy a-energy b)
    rw [eq_div_iff (sub_ne_zero.mpr gap)]
    constructor <;> intro h <;> linear_combination h
  have nz : P ≠ 0 := fun z => pos.ne ((root 0).mp (by rw [z,map_zero]))
  apply (attainable_iff _).mpr
  refine ⟨P,nz,Set.ext fun s => ?_⟩
  change s=t ↔ 0<s ∧ (value s P=0 ∨ value (-s) P=0)
  rw [root,root]
  constructor
  · rintro rfl; exact ⟨pos,Or.inl rfl⟩
  · rintro ⟨hs,eq | eq⟩
    · exact eq
    · exfalso
      linarith only [eq,pos,hs]

/-- Disjointness of the individual spectra is unnecessary for exact finite prescriptions. -/
theorem finite_isolated_orders (T : Finset ℝ) (h : ∀ t ∈ T, Attainable {t}) : Attainable (↑T : Set ℝ) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa only [Finset.coe_empty] using attainable_empty
  | insert t T _ ih =>
    have rest := ih fun u hu => h u (mem_insert_of_mem hu)
    rw [Finset.coe_insert,← Set.singleton_union]
    exact (attainable_union_inter (h t (mem_insert_self _ _)) rest).1

#print axioms separate_harmonics
#print axioms isolated_ratio
#print axioms finite_isolated_orders

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
