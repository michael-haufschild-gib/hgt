import GaloisForLFunctions.RHTower.KloostermanComposite
import GaloisForLFunctions.RHTower.QuadraticGaussSumFourthPower
import GaloisForLFunctions.RHTower.WeilKloostermanArtinSchreier
import GaloisForLFunctions.RHTower.HalfWeightSquareRoots
import GaloisForLFunctions.RHTower.KloostermanZeta
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-!
# Conductor fibres and a composite Kloosterman bound

Constant unit fibres descend common coefficient factors exactly. Stationary
fibres reduce to square roots of one. Prime-power induction and CRT retain
the actual frequency gcd and give `‖S(a,b;M)‖³ ≤ 512 τ(M)³ M² gcd(M,a,b)`.
-/

namespace GaloisForLFunctions.Goldbach

open Finset RHTower.Sieve
open scoped BigOperators

noncomputable section
set_option autoImplicit false

/-- Reduction from the product modulus to its first positive factor. -/
def kloostermanUnitReduction (q d : ℕ+) :
    (ZMod ((q : ℕ) * (d : ℕ)))ˣ →* (ZMod (q : ℕ))ˣ :=
  ZMod.unitsMap (dvd_mul_right (q : ℕ) (d : ℕ))

/-- The exact multiplicity of a unit lifted through modulus reduction. -/
def kloostermanLiftMultiplicity (q d : ℕ+) : ℕ :=
  Fintype.card (kloostermanUnitReduction q d).ker

theorem kloostermanUnitReduction_surjective (q d : ℕ+) :
    Function.Surjective (kloostermanUnitReduction q d) :=
  ZMod.unitsMap_surjective (dvd_mul_right (q : ℕ) (d : ℕ))

/-- A lifted unit is determined by its residue and its quotient label. -/
theorem kloostermanLiftMultiplicity_le (q d : ℕ+) :
    kloostermanLiftMultiplicity q d ≤ (d : ℕ) := by
  let N : ℕ := (q : ℕ) * (d : ℕ)
  let f : (kloostermanUnitReduction q d).ker → Fin (d : ℕ) := fun u =>
    ⟨((u.1 : ZMod N).val / (q : ℕ)),
      Nat.div_lt_of_lt_mul (ZMod.val_lt (u.1 : ZMod N))⟩
  have hf : Function.Injective f := by
    intro u v huv
    have hquot : (u.1 : ZMod N).val / (q : ℕ) =
        (v.1 : ZMod N).val / (q : ℕ) := congrArg Fin.val huv
    have hred : kloostermanUnitReduction q d u.1 =
        kloostermanUnitReduction q d v.1 := u.2.trans v.2.symm
    have hcast : (((u.1 : ZMod N).val : ℕ) : ZMod (q : ℕ)) =
        (((v.1 : ZMod N).val : ℕ) : ZMod (q : ℕ)) := by
      have hval := congrArg Units.val hred
      change ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ)) (ZMod (q : ℕ))
          (u.1 : ZMod N) =
        ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ)) (ZMod (q : ℕ))
          (v.1 : ZMod N) at hval
      rwa [← ZMod.natCast_zmod_val (u.1 : ZMod N),
        ← ZMod.natCast_zmod_val (v.1 : ZMod N), map_natCast, map_natCast] at hval
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ (q : ℕ)).mp hcast
    apply Subtype.ext
    apply Units.ext
    apply ZMod.val_injective
    rw [← Nat.mod_add_div (u.1 : ZMod N).val (q : ℕ),
      ← Nat.mod_add_div (v.1 : ZMod N).val (q : ℕ), hquot, hmod]
  simpa only [kloostermanLiftMultiplicity, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

/-- Multiplying the phase by the second modulus factor removes that factor. -/
theorem stdAddChar_factor_reduction (q d : ℕ+)
    (z : ZMod ((q : ℕ) * (d : ℕ))) :
    ZMod.stdAddChar (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * z) =
      ZMod.stdAddChar
        (ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ)) (ZMod (q : ℕ)) z) := by
  have h := RHTower.HalfWeight.stdAddChar_intCast_mul
    (N := (q : ℕ) * (d : ℕ)) (d := (q : ℕ)) (e := (d : ℕ))
    (by push_cast; rfl) (z.val : ℤ)
  have hz : ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ))
      (ZMod (q : ℕ)) z = (z.val : ZMod (q : ℕ)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [hz]
  simpa only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm] using h

/-- Every observation of the reduced unit has the same exact lift multiplicity. -/
theorem sum_kloostermanUnitReduction (q d : ℕ+)
    (f : (ZMod (q : ℕ))ˣ → ℂ) :
    (∑ x : (ZMod ((q : ℕ) * (d : ℕ)))ˣ,
      f (kloostermanUnitReduction q d x)) =
        (kloostermanLiftMultiplicity q d : ℂ) * ∑ y : (ZMod (q : ℕ))ˣ, f y := by
  classical
  let π := kloostermanUnitReduction q d
  let φ : Additive (ZMod ((q : ℕ) * (d : ℕ)))ˣ →+
      Additive (ZMod (q : ℕ))ˣ :=
    { toFun := fun x => Additive.ofMul (π (Additive.toMul x))
      map_zero' := π.map_one
      map_add' := π.map_mul }
  have h := RHTower.WeilKloosterman.sum_comp_eq_card_ker_mul φ
    (fun y => f (Additive.toMul y))
  have hi : univ.image φ = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨x, hx⟩ := kloostermanUnitReduction_surjective q d (Additive.toMul y)
    exact mem_image.mpr ⟨Additive.ofMul x, mem_univ _, hx⟩
  have hk : (univ.filter (fun x => φ x = 0)).card =
      kloostermanLiftMultiplicity q d := by
    rw [kloostermanLiftMultiplicity, Fintype.card_subtype]
    apply card_bij (fun x _ => Additive.toMul x)
    · intro x hx
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩
    · intro x _ y _ hxy
      exact hxy
    · intro y hy
      exact ⟨Additive.ofMul y,
        mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2⟩, rfl⟩
  rw [hi, hk] at h
  let EA : Additive (ZMod ((q : ℕ) * (d : ℕ)))ˣ ≃
      (ZMod ((q : ℕ) * (d : ℕ)))ˣ :=
    ⟨Additive.toMul, Additive.ofMul, fun _ => rfl, fun _ => rfl⟩
  let EB : Additive (ZMod (q : ℕ))ˣ ≃ (ZMod (q : ℕ))ˣ :=
    ⟨Additive.toMul, Additive.ofMul, fun _ => rfl, fun _ => rfl⟩
  have hsA := Fintype.sum_equiv EA (fun a => f (Additive.toMul (φ a)))
    (fun x => f (kloostermanUnitReduction q d x)) (fun _ => rfl)
  have hsB := Fintype.sum_equiv EB (fun b => f (Additive.toMul b)) f (fun _ => rfl)
  rw [hsA, hsB] at h
  simpa only [nsmul_eq_mul] using h

/-- A common coefficient factor descends with the exact unit-fibre multiplicity. -/
theorem kloostermanSum_factor_lift (q d : ℕ+) (m n : ℤ) :
    kloostermanSum ((q : ℕ) * (d : ℕ))
      (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * (m : ZMod ((q : ℕ) * (d : ℕ))))
      (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * (n : ZMod ((q : ℕ) * (d : ℕ)))) =
        (kloostermanLiftMultiplicity q d : ℂ) *
          kloostermanSum (q : ℕ) (m : ZMod (q : ℕ)) (n : ZMod (q : ℕ)) := by
  have hphase (x : (ZMod ((q : ℕ) * (d : ℕ)))ˣ) :
      kloostermanPhase ((q : ℕ) * (d : ℕ))
        (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * m)
        (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * n) x =
      kloostermanPhase (q : ℕ) m n (kloostermanUnitReduction q d x) := by
    unfold kloostermanPhase
    rw [show (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * m) * x +
        (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * n) * ↑x⁻¹ =
        ((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) *
          ((m : ZMod ((q : ℕ) * (d : ℕ))) * x + n * ↑x⁻¹) by ring]
    rw [stdAddChar_factor_reduction]
    apply congrArg ZMod.stdAddChar
    simp only [map_add, map_mul, map_intCast]
    change (m : ZMod (q : ℕ)) * ↑(kloostermanUnitReduction q d x) +
        (n : ZMod (q : ℕ)) * ↑(kloostermanUnitReduction q d x⁻¹) = _
    rw [map_inv]
  unfold kloostermanSum
  simp_rw [hphase]
  exact sum_kloostermanUnitReduction q d
    (kloostermanPhase (q : ℕ) (m : ZMod (q : ℕ)) (n : ZMod (q : ℕ)))

/-- Descending a common coefficient factor costs at most that factor. -/
theorem norm_kloostermanSum_factor_lift_le (q d : ℕ+) (m n : ℤ) :
    ‖kloostermanSum ((q : ℕ) * (d : ℕ))
      (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * (m : ZMod ((q : ℕ) * (d : ℕ))))
      (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * (n : ZMod ((q : ℕ) * (d : ℕ))))‖ ≤
        (d : ℕ) * ‖kloostermanSum (q : ℕ) (m : ZMod (q : ℕ)) (n : ZMod (q : ℕ))‖ := by
  rw [kloostermanSum_factor_lift, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (kloostermanLiftMultiplicity_le q d)) (norm_nonneg _)

/-- The ring reduction underlying the unit-fibre map. -/
def kloostermanResidueReduction (q d : ℕ+) :
    ZMod ((q : ℕ) * (d : ℕ)) →+* ZMod (q : ℕ) :=
  ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ)) (ZMod (q : ℕ))

/-- The smaller residue vanishes exactly when the lifted residue is killed by the factor. -/
theorem kloostermanResidueReduction_eq_zero_iff (q d : ℕ+)
    (z : ZMod ((q : ℕ) * (d : ℕ))) :
    kloostermanResidueReduction q d z = 0 ↔
      ((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * z = 0 := by
  have hz : kloostermanResidueReduction q d z = (z.val : ZMod (q : ℕ)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  calc
    _ ↔ (q : ℕ) ∣ z.val := by rw [hz, ZMod.natCast_eq_zero_iff]
    _ ↔ (q : ℕ) * (d : ℕ) ∣ (d : ℕ) * z.val := by
      conv_rhs => lhs; rw [Nat.mul_comm]
      exact (Nat.mul_dvd_mul_iff_left d.pos).symm
    _ ↔ (((d : ℕ) * z.val : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
    _ ↔ _ := by rw [Nat.cast_mul, ZMod.natCast_zmod_val]

/-- Units on which the lifted derivative of a Kloosterman phase vanishes. -/
def kloostermanStationaryUnits (q d : ℕ+)
    (a : ZMod ((q : ℕ) * (d : ℕ)))
    (b : (ZMod ((q : ℕ) * (d : ℕ)))ˣ) :
    Finset (ZMod ((q : ℕ) * (d : ℕ)))ˣ :=
  univ.filter fun x =>
    ((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) *
      (a * x - (b : ZMod ((q : ℕ) * (d : ℕ))) * ↑x⁻¹) = 0

/-- Stationarity is the literal square equation at the reduced modulus. -/
theorem mem_kloostermanStationaryUnits_iff (q d : ℕ+)
    (a : ZMod ((q : ℕ) * (d : ℕ)))
    (b x : (ZMod ((q : ℕ) * (d : ℕ)))ˣ) :
    x ∈ kloostermanStationaryUnits q d a b ↔
      kloostermanResidueReduction q d a *
          (kloostermanUnitReduction q d x : ZMod (q : ℕ)) ^ 2 =
        (kloostermanUnitReduction q d b : ZMod (q : ℕ)) := by
  let N : ℕ := (q : ℕ) * (d : ℕ)
  have hxy : (x : ZMod N) * (↑x⁻¹ : ZMod N) = 1 := by simp
  have he : ((d : ℕ) : ZMod N) * (a * x - (b : ZMod N) * ↑x⁻¹) =
      (((d : ℕ) : ZMod N) * (a * (x : ZMod N) ^ 2 - b)) * ↑x⁻¹ := by
    linear_combination -((d : ℕ) : ZMod N) * a * (x : ZMod N) * hxy
  simp only [kloostermanStationaryUnits, mem_filter, mem_univ, true_and]
  rw [he, (x⁻¹).isUnit.mul_left_eq_zero,
    ← kloostermanResidueReduction_eq_zero_iff]
  simp only [map_sub, map_mul, map_pow, sub_eq_zero]
  rfl

/-- The square-root multiplicity of the identity in the reduced unit group. -/
def kloostermanUnitSquareRootCount (q : ℕ+) : ℕ :=
  (univ.filter (fun u : (ZMod (q : ℕ))ˣ => u ^ 2 = 1)).card

theorem kloostermanUnitSquareRootCount_le_rootCard (q : ℕ+) :
    kloostermanUnitSquareRootCount q ≤ RHTower.HalfWeight.rootCard 1 (q : ℕ) := by
  classical
  apply card_le_card_of_injOn (fun u : (ZMod (q : ℕ))ˣ => (u : ZMod (q : ℕ)))
  · intro u hu
    have h := congrArg Units.val (mem_filter.mp hu).2
    exact mem_filter.mpr ⟨mem_univ _, by simpa only [pow_two, Units.val_mul, Units.val_one,
      Int.cast_one] using h⟩
  · intro u _ v _ huv
    exact Units.ext huv

/-- Normalizing by an actual stationary point leaves only roots of one and lift multiplicity. -/
theorem card_kloostermanStationaryUnits_le_liftMultiplicity (q d : ℕ+)
    (a : ZMod ((q : ℕ) * (d : ℕ)))
    (b : (ZMod ((q : ℕ) * (d : ℕ)))ˣ) :
    (kloostermanStationaryUnits q d a b).card ≤
      kloostermanLiftMultiplicity q d * kloostermanUnitSquareRootCount q := by
  classical
  let π := kloostermanUnitReduction q d
  let ρ := kloostermanResidueReduction q d
  let T := kloostermanStationaryUnits q d a b
  rcases T.eq_empty_or_nonempty with ht | ⟨y, hy⟩
  · rw [show kloostermanStationaryUnits q d a b = ∅ from ht]
    simp
  have hsol (x : (ZMod ((q : ℕ) * (d : ℕ)))ˣ) (hx : x ∈ T) :
      ρ a * (π x : ZMod (q : ℕ)) ^ 2 = (π b : ZMod (q : ℕ)) :=
    (mem_kloostermanStationaryUnits_iff q d a b x).mp hx
  have ha : IsUnit (ρ a) := isUnit_of_mul_isUnit_left
    (show IsUnit (ρ a * (π y : ZMod (q : ℕ)) ^ 2) from
      (hsol y hy).symm ▸ (π b).isUnit)
  obtain ⟨u, hu⟩ := ha
  let W : Finset (ZMod ((q : ℕ) * (d : ℕ)))ˣ :=
    univ.filter fun x => (π x) ^ 2 = 1
  have hinj : T.card ≤ W.card := by
    apply card_le_card_of_injOn (fun x => x * y⁻¹)
    · intro x hx
      have he := (hsol x hx).trans (hsol y hy).symm
      rw [← hu] at he
      have he' := congrArg (fun z : ZMod (q : ℕ) => u.inv * z) he
      have hs : (π x) ^ 2 = (π y) ^ 2 := by
        apply Units.ext
        simpa only [pow_two, Units.val_mul, ← mul_assoc, u.inv_val, one_mul] using he'
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      simp only [map_mul, map_inv, mul_pow, hs, inv_pow, mul_inv_cancel]
    · intro x _ z _ hxz
      exact mul_right_cancel hxz
  have hW : W.card = kloostermanLiftMultiplicity q d *
      kloostermanUnitSquareRootCount q := by
    have h := sum_kloostermanUnitReduction q d
      (fun u => if u ^ 2 = 1 then (1 : ℂ) else 0)
    simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h
  exact hinj.trans_eq hW

/-- The whole stationary fibre, with the residue-lift cost retained. -/
theorem card_kloostermanStationaryUnits_le_rootCard (q d : ℕ+)
    (a : ZMod ((q : ℕ) * (d : ℕ)))
    (b : (ZMod ((q : ℕ) * (d : ℕ)))ˣ) :
    (kloostermanStationaryUnits q d a b).card ≤
      (d : ℕ) * RHTower.HalfWeight.rootCard 1 (q : ℕ) := by
  exact (card_kloostermanStationaryUnits_le_liftMultiplicity q d a b).trans
    (Nat.mul_le_mul (kloostermanLiftMultiplicity_le q d)
      (kloostermanUnitSquareRootCount_le_rootCard q))

/-- Dyadic stationary phase, including the small moduli, with its complete lift cost. -/
theorem norm_kloostermanSum_two_pow_unit_le (k : ℕ)
    (a : ZMod (2 ^ k)) (b : (ZMod (2 ^ k))ˣ) :
    ‖kloostermanSum (2 ^ k) a b‖ ≤ 8 * (2 : ℝ) ^ ((k + 1) / 2) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let j := (k + 1) / 2
  let m := k - j
  let q : ℕ+ := ⟨2 ^ m, by positivity⟩
  let d : ℕ+ := ⟨2 ^ j, by positivity⟩
  have hqd : (q : ℕ) * (d : ℕ) = 2 ^ k := by
    change 2 ^ m * 2 ^ j = 2 ^ k
    rw [← pow_add]
    congr 1
    dsimp [m, j]
    omega
  have hs (N : ℕ) (hN : N = 2 ^ k) :
      letI : NeZero N := ⟨by rw [hN]; exact pow_ne_zero _ (by norm_num)⟩
      ∀ x y : ZMod N, kloostermanSum N x y =
        ∑ u : (ZMod N)ˣ, if (2 : ZMod N) ^ j * (x * u - y * ↑u⁻¹) = 0
          then kloostermanPhase N x y u else 0 := by
    subst N
    exact RHTower.KloostermanComposite.kloostermanSum_stationary
      2 k j (by dsimp [j]; omega)
  have hbound : ∀ (x : ZMod ((q : ℕ) * (d : ℕ)))
      (y : (ZMod ((q : ℕ) * (d : ℕ)))ˣ),
      ‖kloostermanSum ((q : ℕ) * (d : ℕ)) x y‖ ≤ 8 * (2 : ℝ) ^ j := by
    intro x y
    have hphase : ‖kloostermanSum ((q : ℕ) * (d : ℕ)) x y‖ ≤
        ((kloostermanStationaryUnits q d x y).card : ℝ) := by
      rw [hs _ hqd x y, ← sum_filter]
      refine (norm_sum_le _ _).trans_eq ?_
      simp only [norm_kloostermanPhase, sum_const, nsmul_eq_mul, mul_one]
      congr 1
      have hd : ((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) =
          (2 : ZMod ((q : ℕ) * (d : ℕ))) ^ j := by
        change (((2 : ℕ) ^ j : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) = _
        exact Nat.cast_pow 2 j
      simp only [kloostermanStationaryUnits, hd]
    have hc := card_kloostermanStationaryUnits_le_rootCard q d x y
    have hr : RHTower.HalfWeight.rootCard 1 (q : ℕ) ≤ 8 := by
      simpa only [q, PNat.mk_coe, Int.natAbs_one, mul_one] using
        (RHTower.HalfWeight.rootCard_le (p := 2) (n := 1) (by norm_num) m)
    have hcard : (kloostermanStationaryUnits q d x y).card ≤ (d : ℕ) * 8 :=
      hc.trans (Nat.mul_le_mul_left (d : ℕ) hr)
    refine hphase.trans ?_
    have hreal := (Nat.cast_le (α := ℝ)).mpr hcard
    simpa only [d, PNat.mk_coe, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      mul_comm] using hreal
  have htransport (N : ℕ) (hN : N = (q : ℕ) * (d : ℕ)) :
      letI : NeZero N := ⟨by rw [hN]; positivity⟩
      ∀ (x : ZMod N) (y : (ZMod N)ˣ),
        ‖kloostermanSum N x y‖ ≤ 8 * (2 : ℝ) ^ j := by
    subst N
    exact hbound
  exact htransport (2 ^ k) hqd.symm a b

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩

/-- The local cubic budget; only the dyadic prime pays the factor 512. -/
theorem norm_kloostermanSum_prime_pow_unit_cube_le (p : Nat.Primes) (k : ℕ)
    (a : ZMod ((p : ℕ) ^ k)) (b : (ZMod ((p : ℕ) ^ k))ˣ) :
    ‖kloostermanSum ((p : ℕ) ^ k) a b‖ ^ 3 ≤
      (if (p : ℕ) = 2 then (512 : ℝ) else 1) *
        (k + 1 : ℝ) ^ 3 * (p : ℝ) ^ (2 * k) := by
  rcases p with ⟨p, hp⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hcost : (1 : ℝ) ≤ if p = 2 then 512 else 1 := by
    split_ifs <;> norm_num
  rcases k with _ | _ | k
  · have h := norm_kloostermanSum_le_totient (p ^ 0) a b
    have h1 : ‖kloostermanSum (p ^ 0) a b‖ ≤ 1 := by simpa only [pow_zero,
      Nat.totient_one, Nat.cast_one] using h
    simpa only [Nat.cast_zero, zero_add, one_pow, mul_zero, pow_zero, mul_one]
      using (pow_le_pow_left₀ (norm_nonneg _) h1 3).trans (by simpa using hcost)
  · let N := p ^ (0 + 1)
    letI : Fact N.Prime := ⟨by simpa only [N, Nat.zero_add, Nat.pow_one] using hp⟩
    by_cases hp2 : p = 2
    · have h : ‖kloostermanSum N a b‖ ≤ 1 :=
        (norm_kloostermanSum_le_totient N a b).trans_eq (by simp [N, hp2])
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h 3
      exact h3.trans (by norm_num [hp2])
    · have hN2 : N ≠ 2 := by simpa only [N, Nat.zero_add, Nat.pow_one] using hp2
      have h : ‖kloostermanSum N a b‖ ≤ 2 * Real.sqrt p := by
        calc
          _ ≤ 2 * Real.sqrt N :=
            _root_.RHTower.norm_kloostermanSum_le_weil N hN2 a b.isUnit.ne_zero
          _ = 2 * Real.sqrt p := by simp only [N, Nat.zero_add, Nat.pow_one]
      have hsq : ‖kloostermanSum N a b‖ ^ 2 ≤ 4 * (p : ℝ) := by
        calc
          _ ≤ (2 * Real.sqrt p) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
          _ = 4 * (p : ℝ) := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg p)]; ring
      have hlin : ‖kloostermanSum N a b‖ ≤ 2 * (p : ℝ) :=
        h.trans (mul_le_mul_of_nonneg_left (show Real.sqrt (p : ℝ) ≤ p from by
          nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p : ℝ),
            mul_nonneg (sub_nonneg.mpr hp1) (Nat.cast_nonneg p)]) (by norm_num))
      have hcube : ‖kloostermanSum N a b‖ ^ 3 ≤ 8 * (p : ℝ) ^ 2 := by
        calc
          _ = ‖kloostermanSum N a b‖ ^ 2 * ‖kloostermanSum N a b‖ := by ring
          _ ≤ (4 * (p : ℝ)) * (2 * (p : ℝ)) :=
            mul_le_mul hsq hlin (norm_nonneg _) (by positivity)
          _ = 8 * (p : ℝ) ^ 2 := by ring
      refine hcube.trans_eq ?_
      norm_num [hp2]
  · let j := (k + 2 + 1) / 2
    have he : j * 3 ≤ 2 * (k + 2) := by dsimp [j]; omega
    have hepow : (p : ℝ) ^ (j * 3) ≤ (p : ℝ) ^ (2 * (k + 2)) :=
      pow_le_pow_right₀ hp1 he
    have hk1 : (1 : ℝ) ≤ (k + 2 + 1 : ℝ) ^ 3 := by
      have h1 : (1 : ℝ) ≤ k + 2 + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h1 3
    by_cases hp2 : p = 2
    · subst p
      have h := norm_kloostermanSum_two_pow_unit_le (k + 2) a b
      have h3 : ‖kloostermanSum (2 ^ (k + 2)) a b‖ ^ 3 ≤
          512 * (2 : ℝ) ^ (2 * (k + 2)) := by
        calc
          _ ≤ (8 * (2 : ℝ) ^ j) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) h 3
          _ = 512 * (2 : ℝ) ^ (j * 3) := by rw [mul_pow, ← pow_mul]; norm_num
          _ ≤ 512 * (2 : ℝ) ^ (2 * (k + 2)) :=
            mul_le_mul_of_nonneg_left hepow (by norm_num)
      push_cast
      exact h3.trans (by nlinarith [mul_nonneg (by positivity :
        (0 : ℝ) ≤ 512 * (2 : ℝ) ^ (2 * (k + 2))) (sub_nonneg.mpr hk1)])
    · have h := RHTower.KloostermanComposite.norm_kloostermanSum_prime_pow_le
        p (k + 2) j hp2 (by dsimp [j]; omega) (by dsimp [j]; omega) a b.isUnit
      have h3 : ‖kloostermanSum (p ^ (k + 2)) a b‖ ^ 3 ≤
          8 * (p : ℝ) ^ (2 * (k + 2)) := by
        calc
          _ ≤ (2 * (p : ℝ) ^ j) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) h 3
          _ = 8 * (p : ℝ) ^ (j * 3) := by rw [mul_pow, ← pow_mul]; norm_num
          _ ≤ 8 * (p : ℝ) ^ (2 * (k + 2)) :=
            mul_le_mul_of_nonneg_left hepow (by norm_num)
      have hk8 : (8 : ℝ) ≤ (k + 2 + 1 : ℝ) ^ 3 := by
        have h2 : (2 : ℝ) ≤ k + 2 + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3
        norm_num only at h
        exact h
      simp only [if_neg hp2, one_mul]
      push_cast
      refine h3.trans ?_
      have hmul := mul_le_mul_of_nonneg_right hk8
        (by positivity : 0 ≤ (p : ℝ) ^ (2 * (k + 2)))
      exact hmul.trans_eq (by ring)

open RHTower.KloostermanZeta

/-- The unit-twist envelope is attained by an actual residue. -/
theorem kloostermanMaximum_attained (q : ℕ+) (m n : ℤ) :
    ∃ u : (ZMod (q : ℕ))ˣ,
      kmax m n (q : ℕ) =
        ‖kloostermanSum (q : ℕ) ((u : ZMod (q : ℕ)) * m)
          ((u : ZMod (q : ℕ)) * n)‖ := by
  classical
  obtain ⟨u, _, hu⟩ := univ.exists_max_image
    (fun v : (ZMod (q : ℕ))ˣ =>
      ‖kloostermanSum (q : ℕ) ((v : ZMod (q : ℕ)) * m)
        ((v : ZMod (q : ℕ)) * n)‖) univ_nonempty
  refine ⟨u, le_antisymm ?_ (le_kmax m n (q : ℕ) u.isUnit)⟩
  apply kmax_le
  intro x hx
  obtain ⟨v, rfl⟩ := hx
  exact hu v (mem_univ _)

/-- The actual unit-twist envelope descends with the same common-factor cost. -/
theorem kloostermanMaximum_factor_lift_le (q d : ℕ+) (m n : ℤ) :
    kmax ((d : ℕ) * m) ((d : ℕ) * n) ((q : ℕ) * (d : ℕ)) ≤
      (d : ℕ) * kmax m n (q : ℕ) := by
  apply kmax_le
  intro x hx
  let ρ := kloostermanResidueReduction q d
  have hx' : IsUnit (ρ x) := hx.map ρ
  have hred : ρ x = (x.val : ZMod (q : ℕ)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [map_natCast]
  have hlift := norm_kloostermanSum_factor_lift_le q d
    ((x.val : ℤ) * m) ((x.val : ℤ) * n)
  simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at hlift
  have hr := le_kmax m n (q : ℕ) hx'
  rw [hred] at hr
  have h := hlift.trans (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _))
  simpa only [Int.cast_mul, Int.cast_natCast, mul_left_comm, mul_assoc] using h


/-- Every frequency pair is charged by its actual common divisor with the modulus. -/
theorem kloostermanMaximum_prime_pow_cube_le (p : Nat.Primes) (k : ℕ) (m n : ℤ) :
    kmax m n ((p : ℕ) ^ k) ^ 3 ≤
      (if (p : ℕ) = 2 then (512 : ℝ) else 1) * (k + 1 : ℝ) ^ 3 *
        (p : ℝ) ^ (2 * k) * (Nat.gcd ((p : ℕ) ^ k) (Nat.gcd m.natAbs n.natAbs) : ℝ) := by
  let c : ℝ := if (p : ℕ) = 2 then 512 else 1
  have hc : 1 ≤ c := by dsimp [c]; split_ifs <;> norm_num
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hp0 : (0 : ℝ) ≤ (p : ℕ) := Nat.cast_nonneg _
  induction k generalizing m n with
  | zero =>
      have h := pow_le_pow_left₀ (kmax_nonneg m n 1) (kmax_one m n) 3
      simpa only [pow_zero, Nat.gcd_one_left, Nat.cast_one, Nat.cast_zero, zero_add,
        one_pow, mul_zero, mul_one] using h.trans (by simpa only [one_pow] using hc)
  | succ k ih =>
      by_cases hboth : (p : ℤ) ∣ m ∧ (p : ℤ) ∣ n
      · obtain ⟨m', rfl⟩ := hboth.1
        obtain ⟨n', rfl⟩ := hboth.2
        let q : ℕ+ := ⟨(p : ℕ) ^ k, pow_pos p.property.pos k⟩
        let d : ℕ+ := ⟨(p : ℕ), p.property.pos⟩
        have h := kloostermanMaximum_factor_lift_le q d m' n'
        have hfactor : kmax ((p : ℤ) * m') ((p : ℤ) * n') ((p : ℕ) ^ (k + 1)) ≤
            (p : ℝ) * kmax m' n' ((p : ℕ) ^ k) := by
          simpa only [q, d, PNat.mk_coe, ← pow_succ] using h
        have hcube := pow_le_pow_left₀ (kmax_nonneg _ _ _) hfactor 3
        rw [mul_pow] at hcube
        have hg : Nat.gcd ((p : ℕ) ^ (k + 1))
            (Nat.gcd ((p : ℤ) * m').natAbs ((p : ℤ) * n').natAbs) =
            (p : ℕ) * Nat.gcd ((p : ℕ) ^ k) (Nat.gcd m'.natAbs n'.natAbs) := by
          rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast,
            Nat.gcd_mul_left, pow_succ', Nat.gcd_mul_left]
        have hk : (k + 1 : ℝ) ^ 3 ≤ (k + 2 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 3
        have hcoef : c * (k + 1 : ℝ) ^ 3 * (p : ℝ) ^ (2 * k) *
            (Nat.gcd ((p : ℕ) ^ k) (Nat.gcd m'.natAbs n'.natAbs) : ℝ) ≤
            c * (k + 2 : ℝ) ^ 3 * (p : ℝ) ^ (2 * k) *
            (Nat.gcd ((p : ℕ) ^ k) (Nat.gcd m'.natAbs n'.natAbs) : ℝ) := by
          gcongr
        have hstep := hcube.trans (mul_le_mul_of_nonneg_left
          ((ih m' n').trans hcoef) (by positivity : 0 ≤ (p : ℝ) ^ 3))
        rw [hg, Nat.cast_mul]
        refine hstep.trans_eq ?_
        push_cast
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
        dsimp [c]
        ring
      · let q : ℕ+ := ⟨(p : ℕ) ^ (k + 1), pow_pos p.property.pos _⟩
        obtain ⟨u, hu⟩ := kloostermanMaximum_attained q m n
        let z : (ZMod ((p : ℕ) ^ (k + 1)))ˣ := u
        have hunit : ‖kloostermanSum ((p : ℕ) ^ (k + 1))
            ((z : ZMod ((p : ℕ) ^ (k + 1))) * m)
            ((z : ZMod ((p : ℕ) ^ (k + 1))) * n)‖ ^ 3 ≤
            c * (k + 2 : ℝ) ^ 3 * (p : ℝ) ^ (2 * (k + 1)) := by
          by_cases hn : (p : ℤ) ∣ n
          · have hm : ¬ (p : ℤ) ∣ m := fun hm => hboth ⟨hm, hn⟩
            obtain ⟨v, hv⟩ := z.isUnit.mul (isUnit_intCast_of_not_dvd (k := k + 1) hm)
            rw [kloostermanSum_comm, ← hv]
            simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
              norm_kloostermanSum_prime_pow_unit_cube_le p (k + 1) _ v
          · obtain ⟨v, hv⟩ := z.isUnit.mul (isUnit_intCast_of_not_dvd (k := k + 1) hn)
            rw [← hv]
            simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
              norm_kloostermanSum_prime_pow_unit_cube_le p (k + 1) _ v
        have hgpos : 0 < Nat.gcd ((p : ℕ) ^ (k + 1)) (Nat.gcd m.natAbs n.natAbs) :=
          Nat.gcd_pos_of_pos_left _ (pow_pos p.property.pos _)
        have hg : (1 : ℝ) ≤
            (Nat.gcd ((p : ℕ) ^ (k + 1)) (Nat.gcd m.natAbs n.natAbs) : ℝ) := by
          exact_mod_cast hgpos
        change kmax m n (q : ℕ) ^ 3 ≤ _
        rw [hu]
        push_cast
        have hmul := mul_le_mul_of_nonneg_left hg
          (show 0 ≤ c * (k + 2 : ℝ) ^ 3 * (p : ℝ) ^ (2 * (k + 1)) from by positivity)
        rw [mul_one] at hmul
        exact (hunit.trans hmul).trans_eq (by dsimp [c]; ring)

/-- The sole exceptional local factor in the cubic modulus estimate. -/
def kloostermanDyadicCost (M : ℕ) : ℝ := if 2 ∣ M then 512 else 1

/-- CRT preserves the frequency gcd and pays the dyadic factor only once. -/
theorem kloostermanMaximum_cube_le (m n : ℤ) (M : ℕ) :
    kmax m n M ^ 3 ≤ kloostermanDyadicCost M * (M.divisors.card : ℝ) ^ 3 *
      (M : ℝ) ^ 2 * (Nat.gcd M (Nat.gcd m.natAbs n.natAbs) : ℝ) := by
  have hcost0 (N : ℕ) : 0 ≤ kloostermanDyadicCost N := by
    dsimp [kloostermanDyadicCost]
    split_ifs <;> norm_num
  induction M using Nat.recOnPosPrimePosCoprime with
  | zero => simp [kmax]
  | one =>
      have h := pow_le_pow_left₀ (kmax_nonneg m n 1) (kmax_one m n) 3
      simpa [kloostermanDyadicCost] using h
  | prime_pow p k hp hk =>
      have hτ : (p ^ k).divisors.card = k + 1 := by
        rw [Nat.divisors_prime_pow hp, card_map, card_range]
      have hcost : kloostermanDyadicCost (p ^ k) =
          if p = 2 then (512 : ℝ) else 1 := by
        by_cases hp2 : p = 2
        · subst p
          simp [kloostermanDyadicCost, dvd_pow_self 2 (by omega : k ≠ 0)]
        · have htwo : ¬ 2 ∣ p ^ k := by
            intro h
            have hdiv : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h
            have heq : 2 = p := (hp.eq_one_or_self_of_dvd 2 hdiv).resolve_left (by norm_num)
            exact hp2 heq.symm
          simp only [kloostermanDyadicCost, if_neg htwo, if_neg hp2]
      have h := kloostermanMaximum_prime_pow_cube_le ⟨p, hp⟩ k m n
      rw [hcost, hτ]
      convert h using 1
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, ← pow_mul]
      rw [Nat.mul_comm k 2]
  | coprime a b ha hb hab iha ihb =>
      have hcost : kloostermanDyadicCost (a * b) =
          kloostermanDyadicCost a * kloostermanDyadicCost b := by
        by_cases ha2 : 2 ∣ a
        · have hb2 : ¬ 2 ∣ b := by
            intro hb2
            have h := Nat.dvd_gcd ha2 hb2
            rw [hab.gcd_eq_one] at h
            norm_num at h
          simp only [kloostermanDyadicCost, if_pos ha2, if_neg hb2,
            if_pos (dvd_mul_of_dvd_left ha2 b), mul_one]
        · by_cases hb2 : 2 ∣ b
          · simp only [kloostermanDyadicCost, if_neg ha2, if_pos hb2,
              if_pos (dvd_mul_of_dvd_right hb2 a), one_mul]
          · have hab2 : ¬ 2 ∣ a * b := by
              rw [Nat.prime_two.dvd_mul]
              exact not_or.mpr ⟨ha2, hb2⟩
            simp only [kloostermanDyadicCost, if_neg ha2, if_neg hb2, if_neg hab2,
              one_mul]
      have hg : Nat.gcd (a * b) (Nat.gcd m.natAbs n.natAbs) =
          Nat.gcd a (Nat.gcd m.natAbs n.natAbs) *
            Nat.gcd b (Nat.gcd m.natAbs n.natAbs) := by
        simpa only [Nat.gcd_comm] using
          Nat.Coprime.gcd_mul (Nat.gcd m.natAbs n.natAbs) hab
      have h := pow_le_pow_left₀ (kmax_nonneg m n (a * b)) (kmax_mul m n hab) 3
      rw [mul_pow] at h
      have hprod := mul_le_mul iha ihb
        (pow_nonneg (kmax_nonneg m n b) 3)
        (show 0 ≤ kloostermanDyadicCost a * (a.divisors.card : ℝ) ^ 3 *
          (a : ℝ) ^ 2 * (Nat.gcd a (Nat.gcd m.natAbs n.natAbs) : ℝ) from
            mul_nonneg (mul_nonneg (mul_nonneg (hcost0 a) (by positivity))
              (sq_nonneg _)) (Nat.cast_nonneg _))
      refine (h.trans hprod).trans_eq ?_
      rw [hcost, hab.card_divisors_mul, hg]
      push_cast
      ring

/-- A complete, unconditional composite estimate with the actual frequency gcd. -/
theorem norm_kloostermanSum_cube_le (M : ℕ+)
    (a b : ZMod (M : ℕ)) :
    ‖kloostermanSum (M : ℕ) a b‖ ^ 3 ≤
      512 * ((M : ℕ).divisors.card : ℝ) ^ 3 * (M : ℝ) ^ 2 *
        (Nat.gcd (M : ℕ) (Nat.gcd a.val b.val) : ℝ) := by
  have h := le_kmax (a.val : ℤ) (b.val : ℤ) (M : ℕ) (x := 1) isUnit_one
  simp only [one_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at h
  have hcube := pow_le_pow_left₀ (norm_nonneg _) h 3
  have hbound := kloostermanMaximum_cube_le (a.val : ℤ) (b.val : ℤ) (M : ℕ)
  simp only [Int.natAbs_natCast] at hbound
  have hcost : kloostermanDyadicCost (M : ℕ) ≤ 512 := by
    dsimp [kloostermanDyadicCost]
    split_ifs <;> norm_num
  refine (hcube.trans hbound).trans ?_
  gcongr


end
end GaloisForLFunctions.Goldbach
