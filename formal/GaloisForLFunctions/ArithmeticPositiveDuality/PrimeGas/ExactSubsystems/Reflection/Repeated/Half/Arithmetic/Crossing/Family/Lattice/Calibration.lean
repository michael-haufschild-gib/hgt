import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Ratios
import GaloisForLFunctions.RHTower.GelfondSchneider
import GaloisForLFunctions.HTGeometry.CyclotomicTailPhaseHypertranscendence

/-! # Explicit irrational calibration and finite rational-probe failures -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice

open Finset Real Set
open _root_.HTGeometry (finiteGibbsStateWeight)

variable {I : Type*} [Fintype I]

/-- Gelfond–Schneider excludes every algebraic irrational from the exact list
of exceptional one-frequency ratios. -/
theorem algebraic_irrational_good {r : ℝ} (alg : IsAlgebraic ℚ r) (irr : Irrational r) :
    r ∉ exceptional (fun n : ℕ => (n : ℝ)) := by
  intro bad
  obtain ⟨a,b,ha,hb,aa,ba,ratio⟩ := (ratio_iff r).mp bad
  have bpos := zero_lt_one.trans hb
  have power : b^r=a := by
    rw [rpow_def_of_pos bpos,mul_comm,← (div_eq_iff (log_pos hb).ne').mp ratio,
      exp_log (zero_lt_one.trans ha)]
  have trans := GaloisForLFunctions.RHTower.gelfondSchneiderReal_holds b r bpos hb.ne'
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr ba) ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr alg) irr
  exact trans (by rw [power]; exact aa)

theorem sqrt_two_good : sqrt 2 ∉ exceptional (fun n : ℕ => (n : ℝ)) := by
  apply algebraic_irrational_good _ irrational_sqrt_two
  apply IsIntegral.isAlgebraic
  apply IsIntegral.of_pow (zero_lt_two : 0 < 2)
  rw [sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
  simpa only [map_ofNat] using (isIntegral_algebraMap (R := ℚ) (A := ℝ) (x := (2 : ℚ)))

/-- This is the actual energy of the integer shell with occupation \(k_i\)
in the elementary prime mode \(p\). -/
def primeModes (p : Nat.Primes) (k : I → ℕ) (i : I) : ℝ :=
  energy ⟨p.val ^ k i, pow_pos p.property.pos _⟩

omit [Fintype I] in
private theorem modes_eq (p : Nat.Primes) (k : I → ℕ) :
    primeModes p k = fun i => log (p.val : ℝ)*levels k i+0 := by
  funext i
  change log (((p.val ^ k i : ℕ) : ℝ))=log (p.val : ℝ)*(k i : ℝ)+0
  rw [Nat.cast_pow,log_pow,add_zero,mul_comm]

omit [Fintype I] in
theorem affine_reflects (E : I → ℝ) (a b : ℝ) (ha : a ≠ 0) :
    Reflects (fun i => a*E i+b) ↔ Reflects E := by
  constructor
  · rintro ⟨D,R,h⟩
    refine ⟨(D-2*b)/a,R,fun i => (eq_div_iff ha).mpr ?_⟩
    have hi : a*E i+b+(a*E (R i)+b)=D := h i
    linear_combination hi
  · rintro ⟨D,R,h⟩
    refine ⟨a*D+2*b,R,fun i => ?_⟩
    change a*E i+b+(a*E (R i)+b)=a*D+2*b
    linear_combination a*(h i)

theorem grid_law (k : I → ℕ) (a b d : ℝ) (ha : a ≠ 0) {r : ℝ} (hr : 0 < r)
    (good : r ∉ exceptional (fun n : ℕ => (n : ℝ))) :
    let P := finiteGibbsStateWeight d (fun i => a*levels k i+b)
    lawOrder P 1 ∧ lawOrder P r ↔ d=0 ∨ Reflects (levels k) := by
  dsimp only
  rw [gibbs_order,gibbs_order,one_mul,agrees_affine,agrees_affine,mul_assoc]
  have h := calibrated (fun n : ℕ => (n : ℝ)) k hr good (d*a)
  change (agrees (levels k) (d*a) ∧ agrees (levels k) (r*(d*a)) ↔ d*a=0 ∨ Reflects (levels k)) at h
  simpa only [mul_eq_zero,ha,or_false] using h

/-- The fixed orders \(1,\sqrt2\) recognize split isometry on every asymmetric
spectrum of powers of any prime, with arbitrary multiplicities. -/
theorem prime_law (p : Nat.Primes) (k : I → ℕ) (s : ℂ) :
    let P := finiteGibbsStateWeight (2*s.re-1) (primeModes p k)
    lawOrder P 1 ∧ lawOrder P (sqrt 2) ↔
      (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ∨ Reflects (primeModes p k) := by
  have hp := (log_pos (Nat.one_lt_cast.mpr p.property.one_lt)).ne'
  have mid : 2*s.re-1=0 ↔ s.re=1/2 := by constructor <;> intro h <;> linarith only [h]
  have test := grid_law k (log (p.val : ℝ)) 0 (2*s.re-1) hp (sqrt_pos.mpr (by positivity : (0 : ℝ)<2)) sqrt_two_good
  dsimp only at test ⊢
  rw [modes_eq,test,mid,split_isometric_iff,
    affine_reflects _ _ _ hp]

/-- A finite positive schedule admits one asymmetric blind spectrum precisely when
every probe gives an algebraic power of the chosen prime. -/
theorem schedule_iff (p : Nat.Primes) (T : Finset ℝ) (pos : ∀ t ∈ T, 0 < t) :
    (∃ (n : ℕ) (k : Fin n → ℕ), ¬Reflects (primeModes p k) ∧ ∀ t ∈ T, agrees (primeModes p k) t) ↔
      ∀ t ∈ T, IsAlgebraic ℚ ((p.val : ℝ)^t) := by
  classical
  have hp : (1 : ℝ) < p.val := Nat.one_lt_cast.mpr p.property.one_lt
  have pp := zero_lt_one.trans hp
  constructor
  · rintro ⟨n,k,asym,hit⟩ t ht
    rw [modes_eq,affine_reflects _ _ _ (log_pos hp).ne'] at asym
    have nonzero : n ≠ 0 := by
      rintro rfl
      exact asym ⟨0,Equiv.refl _,fun i => Fin.elim0 i⟩
    have nz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr nonzero
    have reading := hit t ht
    rw [modes_eq,agrees_affine] at reading
    have alg := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp (algebraic_coordinate k asym reading)
    rw [Fintype.card_fin] at alg
    have power : exp ((t*log (p.val : ℝ))/n)^n = (p.val : ℝ)^t := by
      rw [← exp_nat_mul,rpow_def_of_pos pp]
      congr 1
      field_simp
    exact power ▸ alg.pow n
  · intro alg
    let f (t : ℝ) := (p.val : ℝ)^t
    obtain ⟨n,k,asym,hit⟩ := prescribed (T.image f) (by
      intro x hx
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hx
      exact ⟨one_lt_rpow hp (pos t ht),alg t ht⟩)
    refine ⟨n,k,?_,fun t ht => ?_⟩
    · rw [modes_eq,affine_reflects _ _ _ (log_pos hp).ne']
      exact asym
    · rw [modes_eq,agrees_affine]
      simpa only [f,log_rpow pp] using hit (f t) (mem_image_of_mem f ht)

/-- At unit damping an arbitrary finite positive rational schedule can be
simultaneously blind on an asymmetric spectrum of powers of any prescribed prime. -/
theorem rational_schedule (p : Nat.Primes) (T : Finset ℚ) (pos : ∀ q ∈ T, 0 < q) :
    ∃ (n : ℕ) (k : Fin n → ℕ), ¬Reflects (primeModes p k) ∧ ∀ q ∈ T, agrees (primeModes p k) (q : ℝ) := by
  classical
  let U := T.image (fun q : ℚ => (q : ℝ))
  have positive (t : ℝ) (ht : t ∈ U) : 0 < t := by
    obtain ⟨q,hq,rfl⟩ := mem_image.mp ht
    exact Rat.cast_pos.mpr (pos q hq)
  obtain ⟨n,k,asym,pass⟩ := (schedule_iff p U positive).mpr (by
    intro t ht
    obtain ⟨q,hq,rfl⟩ := mem_image.mp ht
    exact GaloisForLFunctions.isAlgebraic_natCast_rpow_rat (pos q hq) p.val)
  exact ⟨n,k,asym,fun q hq => pass q (mem_image_of_mem _ hq)⟩

#print axioms algebraic_irrational_good
#print axioms sqrt_two_good
#print axioms prime_law
#print axioms schedule_iff
#print axioms rational_schedule

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice
