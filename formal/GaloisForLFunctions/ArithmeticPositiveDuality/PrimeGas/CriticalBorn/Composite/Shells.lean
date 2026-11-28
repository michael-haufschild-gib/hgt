import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.ElementaryWave

/-! # Prime tuples compressed onto their positive-integer product shells -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite

open Finset Real

abbrev PrimeAt (x : ℝ) := ↥(primes (cutoff x))

/-- Integer label of one elementary excitation. -/
def primeLabel {x : ℝ} (p : PrimeAt x) : ℕ+ :=
  ⟨p.val,(Nat.mem_primesBelow.mp p.property).2.pos⟩

/-- Composition in the occupation basis multiplies all elementary labels. -/
def productLabel {m : ℕ} {x : ℝ} (q : Fin m → PrimeAt x) : ℕ+ := ∏ i, primeLabel (q i)

def shells (m : ℕ) (x : ℝ) : Finset ℕ+ :=
  univ.image (productLabel (m := m) (x := x))

/-- Ordered-prime multiplicity of one composite shell, including repetitions. -/
def multiplicity (m : ℕ) (x : ℝ) (n : ℕ+) :=
  (univ.filter fun q : Fin m → PrimeAt x => productLabel q=n).card

/-- Grouping a finite sum by products counts all orderings exactly once. -/
theorem sum_fibers {A : Type*} [AddCommMonoid A] (m : ℕ) (x : ℝ) (g : ℕ+ → A) :
    ∑ n ∈ shells m x, multiplicity m x n • g n = ∑ q : Fin m → PrimeAt x, g (productLabel q) := by
  unfold shells
  apply sum_image' (fun q => g (productLabel q))
  intro q _
  rw [multiplicity,←sum_const]
  exact sum_congr rfl fun v hv => congrArg g (mem_filter.mp hv).2.symm

private theorem mass_off {m : ℕ} {x : ℝ} {n : ℕ+} (hn : n∉shells m x) :
    multiplicity m x n=0 := by
  rw [multiplicity,card_eq_zero,filter_eq_empty_iff]
  intro q hq eq
  exact hn (eq ▸ mem_image_of_mem productLabel hq)

/-- The composite state lies in the original gas Hilbert space.
Each shell coefficient is the projection of its equal-amplitude ordered
factorizations onto the normalized constant vector of their fiber. -/
def wave (m : ℕ) (s : ℂ) (x : ℝ) : Gas :=
  ∑ n ∈ shells m x, lp.single 2 n ((sqrt (multiplicity m x n):ℂ)*heat s n)

theorem wave_apply (m : ℕ) (s : ℂ) (x : ℝ) (n : ℕ+) :
    wave m s x n = (sqrt (multiplicity m x n):ℂ)*heat s n := by
  rw [wave,lp.coeFn_sum,Finset.sum_apply]
  simp only [lp.single_apply,Pi.single_apply,sum_ite_eq]
  by_cases h : n∈shells m x
  · rw [if_pos h]
  · rw [if_neg h,mass_off h,Nat.cast_zero,sqrt_zero,Complex.ofReal_zero,zero_mul]

/-- All orderings in the same fiber have the same heat amplitude. -/
theorem heat_product {m : ℕ} {x : ℝ} (s : ℂ) (q : Fin m → PrimeAt x) :
    heat s (productLabel q)=∏ i, heat s (primeLabel (q i)) := by
  let H : ℕ+ →* ℂ := {toFun := heat s,map_one' := by simp [heat,energy],map_mul' := heat_mul s}
  exact map_prod H (fun i => primeLabel (q i)) univ

/-- Projection onto the normalized uniform vector of an ordered-product fiber
gives the composite gas coefficient, including a vanishing empty fiber. -/
theorem uniform_projection (m : ℕ) (s : ℂ) (x : ℝ) (n : ℕ+) :
    (∑ q ∈ univ.filter (fun q : Fin m → PrimeAt x => productLabel q=n),
      (∏ i,heat s (primeLabel (q i)))/(sqrt (multiplicity m x n):ℂ)) = wave m s x n := by
  let F := univ.filter (fun q : Fin m → PrimeAt x => productLabel q=n)
  have same (q : Fin m → PrimeAt x) (hq : q∈F) : (∏ i,heat s (primeLabel (q i)))=heat s n := by
    rw [←heat_product,(mem_filter.mp hq).2]
  change (∑ q ∈ F, _)=_
  rw [sum_congr rfl (fun q hq => congrArg (fun z : ℂ => z/(sqrt (multiplicity m x n):ℂ)) (same q hq)),
    sum_const,nsmul_eq_mul,wave_apply]
  change (multiplicity m x n:ℂ)*(heat s n/(sqrt (multiplicity m x n):ℂ))=_
  by_cases h : multiplicity m x n=0
  · simp [h]
  · have pos : 0<(multiplicity m x n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have nonzero : (sqrt (multiplicity m x n):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sqrt_pos.mpr pos).ne'
    have sq : (sqrt (multiplicity m x n):ℂ)^2=(multiplicity m x n:ℂ) := by
      exact_mod_cast Real.sq_sqrt pos.le
    field_simp [nonzero]
    linear_combination -(heat s n)*sq

#print axioms uniform_projection
#print axioms sum_fibers
#print axioms wave_apply
#print axioms heat_product

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite
