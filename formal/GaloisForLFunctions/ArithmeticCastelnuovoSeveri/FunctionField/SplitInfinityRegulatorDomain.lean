import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentTameNormalization
import Mathlib.Data.PNat.Basic

/-!
# A regulator strip at two Laurent places

Molla's normalized generator (arXiv:2610.23742, Lemma 2.1) uses a positive
regulator R, a half-open strip of width 2R, and the leading coefficient at
one place. We construct the representative on actual pairs of Laurent units.
The fundamental translation can have arbitrary principal-unit parts.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity

open HTGeometry.LoopEisenstein
variable {F : Type*} [Field F]
abbrev LocalUnit (F : Type*) [Field F] := (LaurentSeries F)ˣ

/-- Degree at infinity is the negative of Laurent order in the local uniformizer. -/
def degree (x : LocalUnit F) : ℤ := -(x : LaurentSeries F).order

/-- Leading coefficient of a nonzero Laurent series as a coefficient-field unit. -/
def sign (x : LocalUnit F) : Fˣ :=
  Units.mk0 (x : LaurentSeries F).leadingCoeff (HahnSeries.leadingCoeff_ne_zero.mpr x.ne_zero)

private theorem degree_mul (x y : LocalUnit F) : degree (x*y) = degree x + degree y := by
  simp only [degree, Units.val_mul, HahnSeries.order_mul x.ne_zero y.ne_zero, neg_add]

private theorem sign_mul (x y : LocalUnit F) : sign (x*y) = sign x * sign y := by
  apply Units.ext
  exact HahnSeries.leadingCoeff_mul _ _

/-- Multiplying by a signed monomial changes just degree and leading coefficient. -/
def monomial (c : Fˣ) (d : ℤ) : LocalUnit F := laurentConstantUnit F c * laurentXUnit F ^ (-d)

private theorem monomial_val (c : Fˣ) (d : ℤ) :
    (monomial c d : LaurentSeries F) = HahnSeries.single (-d) (c : F) := by
  rw [monomial, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_laurentXUnit,
    ← RatFunc.single_zpow, coe_laurentConstantUnit]
  change (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (c : F))) * _ = _
  rw [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.single_mul_single,
    zero_add, mul_one]

private theorem degree_monomial (c : Fˣ) (d : ℤ) : degree (monomial c d) = d := by
  rw [degree, monomial_val, HahnSeries.order_single c.ne_zero, neg_neg]

private theorem sign_monomial (c : Fˣ) (d : ℤ) : sign (monomial c d) = c := by
  apply Units.ext
  change (monomial c d : LaurentSeries F).leadingCoeff = _
  rw [monomial_val, HahnSeries.leadingCoeff_of_single]

/-- A local character splits into its signed monomial and principal-unit arguments. -/
def angular (x : LocalUnit F) : LocalUnit F := x * (monomial (sign x) (degree x))⁻¹

private theorem degree_pow (x : LocalUnit F) (k : ℤ) : degree (x^k) = k * degree x := by
  let D : LocalUnit F →* Multiplicative ℤ :=
    { toFun := fun u => Multiplicative.ofAdd (degree u)
      map_one' := by simp [degree]
      map_mul' := fun a b => congrArg Multiplicative.ofAdd (degree_mul a b) }
  exact congrArg Multiplicative.toAdd (D.map_zpow x k)

private theorem sign_pow (x : LocalUnit F) (k : ℤ) : sign (x^k) = sign x ^ k := by
  let S : LocalUnit F →* Fˣ :=
    { toFun := sign
      map_one' := by ext; simp [sign]
      map_mul' := sign_mul }
  exact S.map_zpow x k

theorem angular_invariants (x : LocalUnit F) : degree (angular x) = 0 ∧ sign (angular x) = 1 := by
  rw [angular, ← zpow_neg_one, degree_mul, degree_pow, degree_monomial,
    sign_mul, sign_pow, sign_monomial]
  simp

/-- Every Laurent unit is recovered without loss from degree, leading sign and principal part. -/
theorem reconstruct (x : LocalUnit F) : monomial (sign x) (degree x) * angular x = x := by
  unfold angular
  rw [mul_left_comm, mul_inv_cancel, mul_one]

/-- A pair of unit translates with regulator R and arbitrary local higher coefficients. -/
def generator (R : ℕ+) (u v : LocalUnit F) (w : Fˣ) : LocalUnit F × LocalUnit F :=
  (monomial 1 (R : ℤ) * angular u, monomial w (-(R : ℤ)) * angular v)

theorem generator_invariants (R : ℕ+) (u v : LocalUnit F) (w : Fˣ) :
    degree (generator R u v w).1 = R ∧ degree (generator R u v w).2 = -(R : ℤ) ∧
      sign (generator R u v w).1 = 1 ∧ sign (generator R u v w).2 = w := by
  simp [generator,degree_mul,sign_mul,degree_monomial,sign_monomial,
    (angular_invariants u).1,(angular_invariants u).2,
    (angular_invariants v).1,(angular_invariants v).2]

/-- These generators exhaust all local realizations with normalized first sign. -/
theorem generator_exhausts (R : ℕ+) (e : LocalUnit F × LocalUnit F) :
    (∃ u v w, generator R u v w = e) ↔
      degree e.1 = R ∧ degree e.2 = -(R : ℤ) ∧ sign e.1 = 1 := by
  constructor
  · rintro ⟨u,v,w,rfl⟩
    have h := generator_invariants R u v w
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · rintro ⟨h,k,s⟩
    refine ⟨e.1,e.2,sign e.2,Prod.ext ?_ ?_⟩
    · simpa only [generator,h,s] using reconstruct e.1
    · simpa only [generator,k] using reconstruct e.2

/-- The unique power moving a degree difference into (-R,R]. -/
def exponent (R : ℕ+) (d : ℤ) : ℤ := ((R : ℤ)-d)/(2*(R : ℤ))

theorem exponent_strip_iff (R : ℕ+) (d j : ℤ) :
    (-(R : ℤ) < d+2*(R : ℤ)*j ∧ d+2*(R : ℤ)*j ≤ R) ↔ j = exponent R d := by
  have hp : 0 < 2*(R : ℤ) := by positivity
  rw [eq_comm (a := j), exponent, Int.ediv_eq_iff_of_pos hp]
  constructor <;> rintro ⟨hl,hr⟩ <;> constructor <;> nlinarith only [hl,hr]

theorem exponent_strip (R : ℕ+) (d : ℤ) :
    -(R : ℤ) < d + 2*(R : ℤ)*exponent R d ∧ d + 2*(R : ℤ)*exponent R d ≤ R :=
  (exponent_strip_iff R d _).2 rfl

/-- Multiplying both places by a constant and an integral power of the fundamental unit. -/
def translate (e x : LocalUnit F × LocalUnit F) (c : Fˣ) (j : ℤ) :
    LocalUnit F × LocalUnit F :=
  (monomial c 0 * e.1^j * x.1, monomial c 0 * e.2^j * x.2)

theorem norm_degree_invariant (R : ℕ+) (u v : LocalUnit F) (w c : Fˣ)
    (x : LocalUnit F × LocalUnit F) (j : ℤ) :
    let y := translate (generator R u v w) x c j
    degree y.1 + degree y.2 = degree x.1 + degree x.2 := by
  have h := generator_invariants R u v w
  simp only [translate,degree_mul,degree_pow,degree_monomial,h.1,h.2.1]
  ring

/-- The first sign and half-open strip select exactly one constant and one unit power. -/
theorem normalized_iff (R : ℕ+) (u v : LocalUnit F) (w c : Fˣ)
    (x : LocalUnit F × LocalUnit F) (j : ℤ) :
    let y := translate (generator R u v w) x c j
    (sign y.1 = 1 ∧ -(R : ℤ) < degree y.1-degree y.2 ∧ degree y.1-degree y.2 ≤ R) ↔
      c = (sign x.1)⁻¹ ∧ j = exponent R (degree x.1-degree x.2) := by
  have h := generator_invariants R u v w
  simp only [translate,degree_mul,degree_pow,degree_monomial,zero_add,sign_mul,
    sign_monomial,sign_pow,h.1,h.2.1,h.2.2.1,one_zpow,mul_one]
  rw [show j*(R : ℤ)+degree x.1-(j*(-(R : ℤ))+degree x.2) =
    (degree x.1-degree x.2)+2*(R : ℤ)*j by ring, exponent_strip_iff, mul_eq_one_iff_eq_inv]

/-- Composition of changes of generator adds their exponents and multiplies their constants. -/
theorem translate_comp (e x : LocalUnit F × LocalUnit F) (a b : Fˣ) (i j : ℤ) :
    translate e (translate e x a i) b j = translate e x (b*a) (j+i) := by
  have hm : monomial (b*a) (0 : ℤ) = monomial b 0 * monomial a 0 := by
    simp only [monomial, neg_zero,zpow_zero,mul_one,laurentConstantUnit,map_mul]
  apply Prod.ext <;> simp only [translate,hm,zpow_add] <;> ac_rfl

private theorem translate_id (e x : LocalUnit F × LocalUnit F) :
    translate e x 1 0 = x := by
  apply Prod.ext <;> simp [translate,monomial,laurentConstantUnit]

/-- Normalize the first leading coefficient and balance the two degrees. -/
def representative (R : ℕ+) (e x : LocalUnit F × LocalUnit F) : LocalUnit F × LocalUnit F :=
  translate e x (sign x.1)⁻¹ (exponent R (degree x.1-degree x.2))

/-- Translating the input does not change its normalized pair. -/
theorem representative_translate (R : ℕ+) (u v : LocalUnit F) (w c : Fˣ)
    (x : LocalUnit F × LocalUnit F) (j : ℤ) :
    let e := generator R u v w
    representative R e (translate e x c j) = representative R e x := by
  let e := generator R u v w
  let y := translate e x c j
  let b := (sign y.1)⁻¹
  let k := exponent R (degree y.1-degree y.2)
  have h := (normalized_iff R u v w b y k).2 ⟨rfl,rfl⟩
  change sign (translate e y b k).1 = 1 ∧ _ at h
  dsimp only [y] at h
  rw [translate_comp] at h
  obtain ⟨hc,hj⟩ := (normalized_iff R u v w (b*c) x (k+j)).1 h
  change translate e (translate e x c j) b k = translate e x _ _
  rw [translate_comp,hc,hj]

/-- Equality of representatives is a complete invariant of the constant-and-unit orbit. -/
theorem representative_eq_iff (R : ℕ+) (u v : LocalUnit F) (w : Fˣ)
    (x y : LocalUnit F × LocalUnit F) :
    let e := generator R u v w
    representative R e x = representative R e y ↔ ∃ c j, translate e x c j = y := by
  let e := generator R u v w
  let a := (sign x.1)⁻¹
  let b := (sign y.1)⁻¹
  let i := exponent R (degree x.1-degree x.2)
  let j := exponent R (degree y.1-degree y.2)
  constructor
  · intro h
    change translate e x a i = translate e y b j at h
    have he := congrArg (fun z => translate e z b⁻¹ (-j)) h
    rw [translate_comp,translate_comp,inv_mul_cancel,neg_add_cancel,translate_id] at he
    exact ⟨_,_,he⟩
  · rintro ⟨c,k,rfl⟩
    exact (representative_translate R u v w c x k).symm

/-- Degree form of the simultaneous norm bounds: both coordinates stay within
R/2 of half the total degree. -/
theorem representative_degree_bounds (R : ℕ+) (u v : LocalUnit F) (w : Fˣ)
    (x : LocalUnit F × LocalUnit F) :
    let y := representative R (generator R u v w) x
    let n := degree x.1+degree x.2
    n-R ≤ 2*degree y.1 ∧ 2*degree y.1 ≤ n+R ∧
    n-R ≤ 2*degree y.2 ∧ 2*degree y.2 ≤ n+R := by
  let c := (sign x.1)⁻¹
  let j := exponent R (degree x.1-degree x.2)
  have h := (normalized_iff R u v w c x j).2 ⟨rfl,rfl⟩
  have ht := norm_degree_invariant R u v w c x j
  dsimp only [c,j] at h ht
  dsimp only [representative]
  omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.angular_invariants
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.reconstruct
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.generator_invariants
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.generator_exhausts
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.exponent_strip_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.exponent_strip
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.norm_degree_invariant
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.normalized_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.translate_comp
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.representative_translate
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.representative_eq_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.representative_degree_bounds
