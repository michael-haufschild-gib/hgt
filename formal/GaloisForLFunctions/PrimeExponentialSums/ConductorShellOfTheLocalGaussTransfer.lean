import GaloisForLFunctions.RHTower.Sieve.PeriodicDFTSupport
import GaloisForLFunctions.goldbach.KloostermanConductorReduction
import GaloisForLFunctions.RHTower.MultiplicativeLargeSieve

/-!
# The conductor shell of the nonprincipal Gauss transfer

An induced character of prime-power conductor has exactly one active
frequency among the powers of the prime. Its entire local transfer is a
monomial times the primitive Gauss sum. This gives the nonprincipal
part of Gou's local identity, with exact phase and magnitude.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.PrimeExponentialSums.GaussShell

/-- Unnormalized Fourier coefficient with the positive additive phase. -/
def coeff (n : ℕ) [NeZero n] (F : ZMod n → ℂ) (a : ℕ) :=
  ∑ x, F x * ZMod.stdAddChar ((a : ZMod n)*x)

private abbrev red (m d : ℕ+) :=
  ZMod.castHom (dvd_mul_right (m : ℕ) (d : ℕ)) (ZMod (m : ℕ))

private theorem sum_reduce (m d : ℕ+) (F : ZMod (m : ℕ) → ℂ) :
    ∑ x, F (red m d x) = (d : ℂ)*∑ x, F x := by
  let f := (red m d).toAddMonoidHom
  have hu : univ.image f=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y,hy⟩ := ZMod.castHom_surjective (dvd_mul_right (m : ℕ) (d : ℕ)) x
    exact mem_image.mpr ⟨y,mem_univ _,hy⟩
  have h := RHTower.WeilKloosterman.card_eq_card_ker_mul_card_image f
  rw [hu,card_univ,ZMod.card,ZMod.card,mul_comm (m : ℕ) (d : ℕ)] at h
  have hk := Nat.eq_of_mul_eq_mul_right m.property h
  have he := RHTower.WeilKloosterman.sum_comp_eq_card_ker_mul f F
  rw [hu,← hk,nsmul_eq_mul] at he
  exact he

/-- On resonant frequencies the Fourier coefficient of a pullback grows
by precisely the size of the residue fiber. -/
theorem aligned (m d : ℕ+) (F : ZMod (m : ℕ) → ℂ) (b : ℕ) :
    coeff ((m : ℕ)*d) (fun x => F (red m d x)) ((d : ℕ)*b) = (d : ℂ)*coeff m F b := by
  unfold coeff
  rw [← sum_reduce m d (fun y => F y*ZMod.stdAddChar ((b : ZMod (m : ℕ))*y))]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  rw [Nat.cast_mul,mul_assoc,Goldbach.stdAddChar_factor_reduction,map_mul,map_natCast]

/-- Every other frequency is absent for every signal pulled back from m. -/
theorem unaligned (m d : ℕ+) (F : ZMod (m : ℕ) → ℂ) (a : ℕ) (ha : ¬(d : ℕ)∣a) :
    coeff ((m : ℕ)*d) (fun x => F (red m d x)) a=0 := by
  have ht := RHTower.Sieve.dft_periodic_lift_eq_zero (dvd_mul_right (m : ℕ) (d : ℕ)) F
    (-(a : ZMod ((m : ℕ)*d)))
  have hp : ZMod.stdAddChar (-((m : ZMod ((m : ℕ)*d)) * -(a : ZMod ((m : ℕ)*d)))) ≠ 1 := by
    intro he
    rw [mul_neg,neg_neg] at he
    have hz : (m : ZMod ((m : ℕ)*d))*(a : ZMod ((m : ℕ)*d))=0 := by
      apply ZMod.injective_stdAddChar
      simpa only [AddChar.map_zero_eq_one] using he
    rw [← Nat.cast_mul,ZMod.natCast_eq_zero_iff] at hz
    exact ha (Nat.dvd_of_mul_dvd_mul_left m.property hz)
  simpa only [coeff,ZMod.dft_apply,smul_eq_mul,mul_neg,neg_neg,mul_comm,red] using ht hp

private def pp (p : Nat.Primes) (e : ℕ) : ℕ+ := ⟨p.val^e,pow_pos p.property.pos _⟩

variable (p : Nat.Primes) (j k : ℕ)
local notation "M" => pp p (j+1)
local notation "D" => pp p k

/-- Lift from conductor p^(j+1) to level p^(j+1) p^k. -/
def induced (χ : DirichletCharacter ℂ (M : ℕ)) :=
  DirichletCharacter.changeLevel (dvd_mul_right (M : ℕ) (D : ℕ)) χ

private theorem induced_apply (χ : DirichletCharacter ℂ (M : ℕ)) (x : ZMod ((M : ℕ)*D)) :
    induced p j k χ x=χ (red M D x) := by
  by_cases hu : IsUnit x
  · have he := DirichletCharacter.changeLevel_eq_cast_of_dvd χ
      (dvd_mul_right (M : ℕ) (D : ℕ)) hu.unit
    simpa only [induced,hu.unit_spec,ZMod.castHom_apply] using he
  · have hl : ¬IsUnit (red M D x) := by
      intro h
      apply hu
      rw [← ZMod.natCast_zmod_val x,map_natCast,ZMod.isUnit_iff_coprime] at h
      rw [← ZMod.natCast_zmod_val x,ZMod.isUnit_iff_coprime]
      change Nat.Coprime x.val (p.val^(j+1)*p.val^k)
      change Nat.Coprime x.val (p.val^(j+1)) at h
      rw [← pow_add,Nat.coprime_pow_right_iff (by omega)]
      exact (Nat.coprime_pow_right_iff (Nat.succ_pos j) _ _).mp h
    rw [MulChar.map_nonunit _ hu,MulChar.map_nonunit _ hl]

/-- Gauss coefficient at the v-th prime-power frequency before summation. -/
def sample (χ : DirichletCharacter ℂ (M : ℕ)) (v : ℕ) :=
  coeff ((M : ℕ)*D) (induced p j k χ) (p.val^v)

/-- Only v=k survives, with the primitive Gauss sum multiplied by p^k. -/
theorem one_shell (χ : DirichletCharacter ℂ (M : ℕ)) (hχ : χ.IsPrimitive) (v : ℕ) :
    sample p j k χ v = if v=k then (p.val : ℂ)^k*gaussSum χ ZMod.stdAddChar else 0 := by
  have he : (induced p j k χ : ZMod ((M : ℕ)*D) → ℂ) = fun x => χ (red M D x) :=
    funext (induced_apply p j k χ)
  rw [sample,he]
  rcases lt_or_ge v k with h | h
  · rw [if_neg h.ne]
    exact unaligned M D χ _ (fun hd => (not_le_of_gt h)
      ((Nat.pow_dvd_pow_iff_le_right p.property.one_lt).mp hd))
  · obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add,aligned M D]
    have hG : coeff (M : ℕ) χ (p.val^u) =
        χ⁻¹ ((p.val^u : ℕ) : ZMod (M : ℕ))*gaussSum χ ZMod.stdAddChar :=
      gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ _
    rw [hG]
    cases u with
    | zero => simp [pp]
    | succ u =>
      have hn : ¬IsUnit ((p.val^(u+1) : ℕ) : ZMod (M : ℕ)) := by
        rw [ZMod.isUnit_iff_coprime]
        change ¬Nat.Coprime (p.val^(u+1)) (p.val^(j+1))
        rw [Nat.coprime_pow_right_iff (Nat.succ_pos j),Nat.coprime_comm,
          p.property.coprime_iff_not_dvd]
        exact not_not.mpr (dvd_pow_self _ (Nat.succ_ne_zero _))
      rw [MulChar.map_nonunit _ hn,zero_mul,mul_zero,if_neg (by omega)]

/-- The nonprincipal local series is an entire monomial, valid at every z. -/
theorem hasSum_monomial (χ : DirichletCharacter ℂ (M : ℕ)) (hχ : χ.IsPrimitive) (z : ℂ) :
    HasSum (fun v : ℕ => sample p j k χ v*(z/p.val)^v) (gaussSum χ ZMod.stdAddChar*z^k) := by
  apply (hasSum_ite_eq k (gaussSum χ ZMod.stdAddChar*z^k)).congr_fun
  intro v
  rw [one_shell p j k χ hχ]
  by_cases he : v=k
  · subst v
    rw [if_pos rfl,if_pos rfl,div_pow]
    field_simp [Nat.cast_ne_zero.mpr p.property.ne_zero : (p.val : ℂ)≠0]
  · simp only [he,ite_false,zero_mul]

/-- The exact local norm at arbitrary damping and conductor loss. -/
theorem norm_monomial (χ : DirichletCharacter ℂ (M : ℕ)) (hχ : χ.IsPrimitive) (z : ℂ) :
    ‖gaussSum χ ZMod.stdAddChar*z^k‖ = Real.sqrt (p.val^(j+1) : ℝ)*‖z‖^k := by
  have hg := RHTower.normSq_gaussSum_of_isPrimitive hχ
  have hτ : ‖gaussSum χ ZMod.stdAddChar‖=Real.sqrt (p.val^(j+1) : ℝ) := by
    rw [← Real.sqrt_sq (norm_nonneg (gaussSum χ ZMod.stdAddChar)),hg]
    simp [pp]
  rw [norm_mul,norm_pow,hτ]

end GaloisForLFunctions.PrimeExponentialSums.GaussShell
