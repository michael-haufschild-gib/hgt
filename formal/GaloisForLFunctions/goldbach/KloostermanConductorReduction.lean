import GaloisForLFunctions.RHTower.KloostermanComposite
import GaloisForLFunctions.RHTower.QuadraticGaussSumFourthPower
import GaloisForLFunctions.RHTower.WeilKloostermanArtinSchreier
import GaloisForLFunctions.RHTower.HalfWeightSquareRoots
import GaloisForLFunctions.RHTower.KloostermanZeta
import GaloisForLFunctions.RHTower.Sieve.KloostermanCrossPhaseGeometric
import GaloisForLFunctions.RHTower.Sieve.KuzminLandau
import GaloisForLFunctions.RHTower.SquareResidueQuadraticInterval
import GaloisForLFunctions.RHTower.Sieve.KloostermanRamanujanDivisorSum
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate
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



/-! ## The actual finite interval transform -/

/-- Fourier coefficient of the integer interval starting at `A` with length `L`. -/
def intervalAdditiveFourier (M : ℕ+) (A : ℤ) (L : ℕ) (a : ZMod (M : ℕ)) : ℂ :=
  ∑ j ∈ range L, ZMod.stdAddChar (-a * ((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ))))

/-- Distance of a frequency to either endpoint of its canonical residue interval. -/
def residueEdge (M : ℕ+) (a : ZMod (M : ℕ)) : ℕ :=
  min a.val ((M : ℕ) - a.val)

theorem residueEdge_pos_iff (M : ℕ+) (a : ZMod (M : ℕ)) :
    0 < residueEdge M a ↔ a ≠ 0 := by
  constructor
  · intro h ha
    subst a
    simp [residueEdge] at h
  · intro ha
    have ha0 : 0 < a.val := Nat.pos_of_ne_zero
      (fun h => ha ((ZMod.val_eq_zero a).mp h))
    exact lt_min ha0 (Nat.sub_pos_of_lt (ZMod.val_lt a))

theorem intervalAdditiveFourier_zero (M : ℕ+) (A : ℤ) (L : ℕ) :
    intervalAdditiveFourier M A L 0 = L := by
  simp [intervalAdditiveFourier]

/-- The starting point contributes one unit phase; every endpoint stays in the geometric sum. -/
theorem intervalAdditiveFourier_eq_phase_mul_geometric
    (M : ℕ+) (A : ℤ) (L : ℕ) (a : ZMod (M : ℕ)) :
    intervalAdditiveFourier M A L a =
      ZMod.stdAddChar (-a * (A : ZMod (M : ℕ))) *
        ∑ j ∈ range L, (ZMod.stdAddChar (-a)) ^ j := by
  rw [intervalAdditiveFourier, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [show -a * ((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ))) =
      -a * (A : ZMod (M : ℕ)) + j • (-a) by simp only [nsmul_eq_mul]; ring,
    AddChar.map_add_eq_mul, stdAddChar_nsmul_eq_pow]

/-- Exact sine chord of a finite additive frequency, including frequency zero. -/
theorem norm_stdAddChar_chord_eq (M : ℕ+) (a : ZMod (M : ℕ)) :
    ‖1 - ZMod.stdAddChar a‖ =
      2 * Real.sin (Real.pi * (a.val : ℝ) / (M : ℝ)) := by
  have hM : (0 : ℝ) < (M : ℝ) := by exact_mod_cast M.pos
  have hval : (a.val : ℝ) ≤ (M : ℝ) := by exact_mod_cast (ZMod.val_lt a).le
  have hβ0 : 0 ≤ (a.val : ℝ) / (M : ℝ) := by positivity
  have hβ1 : (a.val : ℝ) / (M : ℝ) ≤ 1 :=
    (div_le_iff₀ hM).mpr (by simpa only [one_mul] using hval)
  have hsin : 0 ≤ Real.sin (Real.pi * (a.val : ℝ) / (M : ℝ)) := by
    rw [mul_div_assoc]
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact mul_nonneg Real.pi_pos.le hβ0
    · nlinarith [Real.pi_pos]
  have hchar : ZMod.stdAddChar a =
      Complex.exp (((2 * Real.pi * (a.val : ℝ) / (M : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    push_cast
    ring
  rw [hchar, RHTower.one_sub_exp_mul_I_eq, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [show (2 * Real.pi * (a.val : ℝ) / (M : ℝ)) / 2 =
    Real.pi * (a.val : ℝ) / (M : ℝ) by ring]
  exact abs_of_nonneg (mul_nonneg (by norm_num) hsin)

/-- The character chord pays for distance from the zero frequency. -/
theorem residueEdge_le_stdAddChar_chord (M : ℕ+) (a : ZMod (M : ℕ)) :
    4 * (residueEdge M a : ℝ) / (M : ℝ) ≤ ‖1 - ZMod.stdAddChar a‖ := by
  by_cases ha : a = 0
  · subst a
    simp [residueEdge]
  have hM : (0 : ℝ) < (M : ℝ) := by exact_mod_cast M.pos
  have he : (0 : ℝ) < (residueEdge M a : ℝ) := by
    exact_mod_cast (residueEdge_pos_iff M a).mpr ha
  have hleft : (residueEdge M a : ℝ) ≤ (a.val : ℝ) := by
    exact_mod_cast min_le_left a.val ((M : ℕ) - a.val)
  have hright : (residueEdge M a : ℝ) + (a.val : ℝ) ≤ (M : ℝ) := by
    have h := Nat.cast_le (α := ℝ) |>.mpr (min_le_right a.val ((M : ℕ) - a.val))
    rw [Nat.cast_sub (ZMod.val_lt a).le] at h
    change (residueEdge M a : ℝ) ≤ (M : ℝ) - (a.val : ℝ) at h
    linarith
  have hβ : (a.val : ℝ) / (M : ℝ) ≤ 1 - (residueEdge M a : ℝ) / (M : ℝ) := by
    have h := (div_le_iff₀ hM).mpr
      (show (residueEdge M a : ℝ) + (a.val : ℝ) ≤ 1 * (M : ℝ) by simpa using hright)
    rw [add_div] at h
    linarith
  have hsin := _root_.RHTower.Sieve.two_mul_le_sin_pi_mul
    (div_pos he hM) (div_le_div_of_nonneg_right hleft hM.le) hβ
  rw [norm_stdAddChar_chord_eq]
  simp only [mul_div_assoc] at hsin ⊢
  linarith

/-- Opposite frequencies have the same character chord. -/
theorem norm_stdAddChar_neg_chord_eq (M : ℕ+) (a : ZMod (M : ℕ)) :
    ‖1 - ZMod.stdAddChar (-a)‖ = ‖1 - ZMod.stdAddChar a‖ := by
  rw [AddChar.map_neg_eq_conj]
  have he : (1 : ℂ) - (starRingEnd ℂ) (ZMod.stdAddChar a) =
      (starRingEnd ℂ) (1 - ZMod.stdAddChar a) := by rw [map_sub, map_one]
  rw [he, Complex.norm_conj]

/-- A finite interval has geometric cancellation at every nonzero frequency. -/
theorem norm_intervalAdditiveFourier_le
    (M : ℕ+) (A : ℤ) (L : ℕ) (a : ZMod (M : ℕ)) :
    ‖intervalAdditiveFourier M A L a‖ ≤
      if a = 0 then (L : ℝ) else (M : ℝ) / (2 * (residueEdge M a : ℝ)) := by
  classical
  by_cases ha : a = 0
  · subst a
    rw [if_pos rfl, intervalAdditiveFourier_zero, Complex.norm_natCast]
  rw [if_neg ha]
  have hne : ZMod.stdAddChar (-a) ≠ (1 : ℂ) := by
    intro h
    exact ha (neg_eq_zero.mp ((stdAddChar_eq_one_iff (M : ℕ) (-a)).mp h))
  have hgeom := _root_.RHTower.norm_geom_sum_le
    (show ‖ZMod.stdAddChar (-a)‖ = 1 by simp) hne L
  rw [intervalAdditiveFourier_eq_phase_mul_geometric, norm_mul]
  rw [show ‖ZMod.stdAddChar (-a * (A : ZMod (M : ℕ)))‖ = 1 by simp, one_mul]
  rw [norm_stdAddChar_neg_chord_eq] at hgeom
  have hM : (0 : ℝ) < (M : ℝ) := by exact_mod_cast M.pos
  have he : (0 : ℝ) < (residueEdge M a : ℝ) := by
    exact_mod_cast (residueEdge_pos_iff M a).mpr ha
  refine hgeom.trans ?_
  calc
    _ ≤ 2 / (4 * (residueEdge M a : ℝ) / (M : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (residueEdge_le_stdAddChar_chord M a)
    _ = (M : ℝ) / (2 * (residueEdge M a : ℝ)) := by field_simp; ring

/-- Translation preserves the norm of the actual finite prefix. -/
theorem norm_intervalAdditiveFourier_eq_prefix
    (M : ℕ+) (A : ℤ) (L : ℕ) (a : ZMod (M : ℕ)) :
    ‖intervalAdditiveFourier M A L a‖ =
      ‖_root_.RHTower.squareResidueLinearPrefix a L‖ := by
  have hfactor : intervalAdditiveFourier M A L a =
      ZMod.stdAddChar (-a * (A : ZMod (M : ℕ))) *
        _root_.RHTower.squareResidueLinearPrefix a L := by
    rw [intervalAdditiveFourier, _root_.RHTower.squareResidueLinearPrefix, mul_sum]
    apply sum_congr rfl
    intro j _
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hfactor, norm_mul,
    show ‖ZMod.stdAddChar (-a * (A : ZMod (M : ℕ)))‖ = 1 by simp, one_mul]

/-- Total Fourier mass after deleting the zero frequency. -/
def intervalNonzeroFourierMass (M : ℕ+) (A : ℤ) (L : ℕ) : ℝ :=
  ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
    ‖intervalAdditiveFourier M A L a‖

/-- The logarithmic budget is uniform in both interval length and starting point. -/
theorem intervalNonzeroFourierMass_le (M : ℕ+) (A : ℤ) (L : ℕ) :
    intervalNonzeroFourierMass M A L ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) := by
  classical
  calc
    _ ≤ ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        2 / ‖1 - ZMod.stdAddChar a‖ := by
      apply sum_le_sum
      intro a ha
      have ha0 := (mem_filter.mp ha).2
      rw [norm_intervalAdditiveFourier_eq_prefix]
      have h := _root_.RHTower.norm_squareResidueLinearPrefix_le_cap a L
      rw [if_neg ha0] at h
      rw [norm_stdAddChar_neg_chord_eq] at h
      exact h.trans (min_le_right _ _)
    _ ≤ ∑ a : ZMod (M : ℕ), 2 / ‖1 - ZMod.stdAddChar a‖ :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ _ := _root_.RHTower.squareResidue_sum_reciprocalChord_le

/-- Positive quotient attached to an actual divisor of the modulus. -/
def modulusDivisorQuotient (M : ℕ+) (d : {d : ℕ // d ∈ (M : ℕ).divisors}) : ℕ+ :=
  ⟨(M : ℕ) / d.val,
    Nat.div_pos (Nat.le_of_dvd M.pos (Nat.dvd_of_mem_divisors d.property))
      (Nat.pos_of_mem_divisors d.property)⟩

/-- Canonical representatives agree with the inverse of the finite cyclic equivalence. -/
theorem finEquiv_symm_val (M : ℕ+) (a : ZMod (M : ℕ)) :
    ((ZMod.finEquiv (M : ℕ)).symm a).val = a.val := by
  rcases M with ⟨n, hn⟩
  cases n with
  | zero => omega
  | succ n => rfl

/-- All frequencies divisible by `d` are exactly the frequencies at modulus `M/d`. -/
def divisorFrequencyEquiv (M : ℕ+) (d : {d : ℕ // d ∈ (M : ℕ).divisors}) :
    ZMod (modulusDivisorQuotient M d : ℕ) ≃
      {a : ZMod (M : ℕ) // d.val ∣ a.val} :=
  (ZMod.finEquiv (modulusDivisorQuotient M d : ℕ)).toEquiv.symm.trans
    (ramanujanMultiplesFinEquiv M.pos d.property)

theorem divisorFrequencyEquiv_apply (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors})
    (a : ZMod (modulusDivisorQuotient M d : ℕ)) :
    (divisorFrequencyEquiv M d a).val = ((d.val * a.val : ℕ) : ZMod (M : ℕ)) := by
  change ((d.val * ((ZMod.finEquiv (modulusDivisorQuotient M d : ℕ)).symm a).val : ℕ) :
    ZMod (M : ℕ)) = _
  rw [finEquiv_symm_val]

/-- A restricted interval character descends exactly, including negative starting points. -/
theorem intervalAdditiveFourier_divisorFrequency (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) (A : ℤ) (L : ℕ)
    (a : ZMod (modulusDivisorQuotient M d : ℕ)) :
    intervalAdditiveFourier M A L (divisorFrequencyEquiv M d a).val =
      intervalAdditiveFourier (modulusDivisorQuotient M d) A L a := by
  let q := modulusDivisorQuotient M d
  letI : NeZero ((M : ℕ) / d.val) := ⟨q.pos.ne'⟩
  have hqd : (q : ℕ) ∣ (M : ℕ) :=
    ⟨d.val, (Nat.div_mul_cancel (Nat.dvd_of_mem_divisors d.property)).symm⟩
  have hreduce (z : ZMod (M : ℕ)) :
      (z.val : ZMod (q : ℕ)) = ZMod.castHom hqd (ZMod (q : ℕ)) z := by
    conv_rhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [divisorFrequencyEquiv_apply, intervalAdditiveFourier, intervalAdditiveFourier]
  apply sum_congr rfl
  intro j _
  have h := stdAddChar_divisorMultiple M.pos d.property
    (-((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ))))
    (⟨a.val, ZMod.val_lt a⟩ : Fin (q : ℕ))
  change ZMod.stdAddChar (((d.val * a.val : ℕ) : ZMod (M : ℕ)) *
      -((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ)))) =
    ZMod.stdAddChar ((a.val : ZMod (q : ℕ)) *
      ((-((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ)))).val : ZMod (q : ℕ))) at h
  rw [hreduce, map_neg, map_add, map_intCast, map_natCast,
    ZMod.natCast_zmod_val] at h
  simpa only [neg_mul, mul_neg] using h

/-- Nonzero interval Fourier mass on the literal divisibility progression. -/
def intervalDivisorFourierMass (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) (A : ℤ) (L : ℕ) : ℝ :=
  ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0 ∧ d.val ∣ a.val),
    ‖intervalAdditiveFourier M A L a‖

/-- Restricting frequencies divides the modulus without any loss in the finite transform. -/
theorem intervalDivisorFourierMass_eq (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) (A : ℤ) (L : ℕ) :
    intervalDivisorFourierMass M d A L =
      intervalNonzeroFourierMass (modulusDivisorQuotient M d) A L := by
  classical
  let e := divisorFrequencyEquiv M d
  have he0 : (e 0).val = 0 := by simp [e, divisorFrequencyEquiv_apply]
  have hzero (a : ZMod (modulusDivisorQuotient M d : ℕ)) :
      (e a).val = 0 ↔ a = 0 := by
    constructor
    · intro ha
      apply e.injective
      exact Subtype.ext (ha.trans he0.symm)
    · rintro rfl
      exact he0
  calc
    _ = ∑ x : {a : ZMod (M : ℕ) // d.val ∣ a.val},
        if x.val = 0 then 0 else ‖intervalAdditiveFourier M A L x.val‖ := by
      rw [intervalDivisorFourierMass,
        ← sum_subtype (univ.filter (fun a : ZMod (M : ℕ) => d.val ∣ a.val))
          (by simp) (fun a => if a = 0 then 0 else ‖intervalAdditiveFourier M A L a‖)]
      simp only [sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0 <;> by_cases hd : d.val ∣ a.val <;> simp [ha, hd]
    _ = ∑ a : ZMod (modulusDivisorQuotient M d : ℕ),
        if (e a).val = 0 then 0 else ‖intervalAdditiveFourier M A L (e a).val‖ :=
      (e.sum_comp (fun x => if x.val = 0 then 0 else
        ‖intervalAdditiveFourier M A L x.val‖)).symm
    _ = _ := by
      rw [intervalNonzeroFourierMass, sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0
      · simp [ha, he0]
      · have hz : (e a).val ≠ 0 := fun h => ha ((hzero a).mp h)
        simp only [if_neg hz, if_pos ha]
        rw [show e a = divisorFrequencyEquiv M d a by rfl,
          intervalAdditiveFourier_divisorFrequency]

/-- The progression-sensitive logarithmic budget pays `M/d`, not `M`. -/
theorem intervalDivisorFourierMass_le (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) (A : ℤ) (L : ℕ) :
    intervalDivisorFourierMass M d A L ≤
      (modulusDivisorQuotient M d : ℝ) * (1 + Real.log (M : ℝ)) := by
  rw [intervalDivisorFourierMass_eq]
  refine (intervalNonzeroFourierMass_le _ A L).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hlog : Real.log (modulusDivisorQuotient M d : ℝ) ≤ Real.log (M : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast (modulusDivisorQuotient M d).pos)
    exact_mod_cast Nat.div_le_self (M : ℕ) d.val
  linarith

/-! ## The two frequency axes -/

/-- The zero second frequency is the actual Ramanujan sum. -/
theorem kloostermanSum_axis_eq_ramanujan (M : ℕ+) (a : ZMod (M : ℕ)) :
    kloostermanSum (M : ℕ) a 0 =
      _root_.RHTower.cglRamanujanAdditiveSum ⟨(M : ℕ), M.pos⟩ a := by
  classical
  unfold kloostermanSum kloostermanPhase _root_.RHTower.cglRamanujanAdditiveSum
  simp only [zero_mul, add_zero]
  refine sum_bij' (fun u _ => (u : ZMod (M : ℕ)))
    (fun b hb => (mem_filter.mp hb).2.unit)
    (fun u _ => mem_filter.mpr ⟨mem_univ _, u.isUnit⟩)
    (fun _ _ => mem_univ _)
    (fun u _ => by ext; simp) (fun b hb => by simp) ?_
  intro u _
  rw [mul_comm]

/-- A unit frequency has the primitive Ramanujan value, at every positive modulus. -/
theorem kloostermanSum_unit_zero_eq_moebius (M : ℕ+) (u : (ZMod (M : ℕ))ˣ) :
    kloostermanSum (M : ℕ) (u : ZMod (M : ℕ)) 0 =
      ((ArithmeticFunction.moebius (M : ℕ) : ℤ) : ℂ) := by
  have hcop : Nat.Coprime (u : ZMod (M : ℕ)).val (M : ℕ) :=
    (ZMod.isUnit_iff_coprime _ _).mp (by
      simpa only [ZMod.natCast_zmod_val] using u.isUnit)
  rw [kloostermanSum_axis_eq_ramanujan,
    cglRamanujanAdditiveSum_eq_gcd_mobiusDivisorSum_sieve]
  change (∑ d ∈ (Nat.gcd (u : ZMod (M : ℕ)).val (M : ℕ)).divisors,
    (d : ℂ) * ((ArithmeticFunction.moebius ((M : ℕ) / d) : ℤ) : ℂ)) = _
  rw [hcop.gcd_eq_one]
  simp

theorem norm_kloostermanSum_unit_zero_le (M : ℕ+) (u : (ZMod (M : ℕ))ˣ) :
    ‖kloostermanSum (M : ℕ) (u : ZMod (M : ℕ)) 0‖ ≤ 1 := by
  rw [kloostermanSum_unit_zero_eq_moebius, Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (M : ℕ))

/-- Conductor fibres give the sharp gcd bound on each Ramanujan axis. -/
theorem norm_kloostermanSum_axis_le_gcd (M : ℕ+) (a : ZMod (M : ℕ)) :
    ‖kloostermanSum (M : ℕ) a 0‖ ≤ (Nat.gcd (M : ℕ) a.val : ℝ) := by
  let g : ℕ+ := ⟨Nat.gcd (M : ℕ) a.val, Nat.gcd_pos_of_pos_left a.val M.pos⟩
  have hgM : (g : ℕ) ∣ (M : ℕ) := Nat.gcd_dvd_left _ _
  have hga : (g : ℕ) ∣ a.val := Nat.gcd_dvd_right _ _
  let q : ℕ+ := ⟨(M : ℕ) / (g : ℕ),
    Nat.div_pos (Nat.le_of_dvd M.pos hgM) g.pos⟩
  have hM : (M : ℕ) = (q : ℕ) * (g : ℕ) := (Nat.div_mul_cancel hgM).symm
  have ha : (g : ℕ) * (a.val / (g : ℕ)) = a.val := Nat.mul_div_cancel' hga
  have hc : Nat.Coprime (a.val / (g : ℕ)) (q : ℕ) := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    apply Nat.mul_left_cancel g.pos
    rw [← Nat.gcd_mul_left, ha]
    have hq : (g : ℕ) * (q : ℕ) = (M : ℕ) := by simpa [Nat.mul_comm] using hM.symm
    rw [hq, Nat.mul_one]
    exact Nat.gcd_comm _ _
  have hu : IsUnit ((a.val / (g : ℕ) : ℕ) : ZMod (q : ℕ)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hc
  have hs : ‖kloostermanSum (q : ℕ)
      ((a.val / (g : ℕ) : ℕ) : ZMod (q : ℕ)) 0‖ ≤ 1 := by
    simpa only [hu.unit_spec] using norm_kloostermanSum_unit_zero_le q hu.unit
  have htransport (N : ℕ) (hN : N = (q : ℕ) * (g : ℕ)) :
      letI : NeZero N := ⟨by rw [hN]; exact Nat.mul_ne_zero q.pos.ne' g.pos.ne'⟩
      ‖kloostermanSum N (a.val : ZMod N) 0‖ ≤ (g : ℝ) := by
    subst N
    have h := norm_kloostermanSum_factor_lift_le q g ((a.val / (g : ℕ) : ℕ) : ℤ) 0
    simp only [Int.cast_natCast, Int.cast_zero, mul_zero] at h
    have hcoef : ((g : ℕ) : ZMod ((q : ℕ) * (g : ℕ))) *
        ((a.val / (g : ℕ) : ℕ) : ZMod ((q : ℕ) * (g : ℕ))) =
          (a.val : ZMod ((q : ℕ) * (g : ℕ))) := by
      rw [← Nat.cast_mul, ha]
    rw [hcoef] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (mul_one _))
  have hgcast : (g : ℝ) = (Nat.gcd (M : ℕ) a.val : ℝ) := rfl
  have ht := htransport (M : ℕ) hM
  rw [hgcast] at ht
  simpa only [ZMod.natCast_zmod_val] using ht


/-! ## Exact divisibility of the frequency gcd -/

/-- Two gcd extractions retain the product factor without a valuation argument. -/
theorem gcd_product_dvd_gcd_product (M b c : ℕ) :
    Nat.gcd M (b * c) ∣ Nat.gcd M b * Nat.gcd M c := by
  let D := Nat.gcd M (b * c)
  have hDM : D ∣ M := Nat.gcd_dvd_left _ _
  have hDbc : D ∣ b * c := Nat.gcd_dvd_right _ _
  have hDgb : D ∣ Nat.gcd M c * b := by
    rw [← Nat.gcd_mul_right]
    exact Nat.dvd_gcd (dvd_mul_of_dvd_left hDM b)
      (by simpa only [Nat.mul_comm] using hDbc)
  have hDgM : D ∣ Nat.gcd M c * M := dvd_mul_of_dvd_right hDM _
  have h := Nat.dvd_gcd hDgM hDgb
  rw [Nat.gcd_mul_left, Nat.mul_comm] at h
  exact h

/-- The three-frequency gcd divides the product of the target gcd and the pair gcd. -/
theorem frequencyGcd_dvd (M a b c : ℕ) :
    Nat.gcd M (Nat.gcd a ((b * c) % M)) ∣
      Nat.gcd M c * Nat.gcd M (Nat.gcd a b) := by
  let D := Nat.gcd M (Nat.gcd a ((b * c) % M))
  have hDM : D ∣ M := Nat.gcd_dvd_left _ _
  have hDa : D ∣ a := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hDmod : D ∣ (b * c) % M :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hDbc : D ∣ b * c := by
    rw [← Nat.mod_add_div (b * c) M]
    exact dvd_add hDmod (dvd_mul_of_dvd_left hDM _)
  have hD : D ∣ Nat.gcd (Nat.gcd M a) (b * c) :=
    Nat.dvd_gcd (Nat.dvd_gcd hDM hDa) hDbc
  have hc : Nat.gcd (Nat.gcd M a) c ∣ Nat.gcd M c :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
      (Nat.gcd_dvd_right _ _)
  have h := hD.trans (gcd_product_dvd_gcd_product (Nat.gcd M a) b c)
  have h' := h.trans (Nat.mul_dvd_mul (dvd_refl (Nat.gcd (Nat.gcd M a) b)) hc)
  simpa only [Nat.gcd_assoc, Nat.mul_comm] using h'

/-- The gcd loss in a Kloosterman frequency is bounded by the actual target gcd. -/
theorem residueFrequencyGcd_le (M : ℕ+) (a b c : ZMod (M : ℕ)) :
    Nat.gcd (M : ℕ) (Nat.gcd a.val (b * c).val) ≤
      Nat.gcd (M : ℕ) c.val * Nat.gcd (M : ℕ) (Nat.gcd a.val b.val) := by
  apply Nat.le_of_dvd
    (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ M.pos) (Nat.gcd_pos_of_pos_left _ M.pos))
  simpa only [ZMod.val_mul] using frequencyGcd_dvd (M : ℕ) a.val b.val c.val


/-! ## Exact finite completion of the inverse graph -/

/-- Number of entries of the actual integer interval in one residue class. -/
def intervalResidueMultiplicity (M : ℕ+) (A : ℤ) (L : ℕ) (x : ZMod (M : ℕ)) : ℕ :=
  ((range L).filter (fun j : ℕ => (A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ)) = x)).card

/-- Finite Fourier inversion retains the exact residue multiplicity. -/
theorem intervalResidueMultiplicity_fourier
    (M : ℕ+) (A : ℤ) (L : ℕ) (x : ZMod (M : ℕ)) :
    (M : ℂ) * (intervalResidueMultiplicity M A L x : ℂ) =
      ∑ a : ZMod (M : ℕ), intervalAdditiveFourier M A L a * ZMod.stdAddChar (a * x) := by
  classical
  symm
  calc
    _ = ∑ j ∈ range L, ∑ a : ZMod (M : ℕ),
        ZMod.stdAddChar (a * (x - ((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ))))) := by
      simp only [intervalAdditiveFourier, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro a _
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ j ∈ range L,
        if (A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ)) = x then (M : ℂ) else 0 := by
      apply sum_congr rfl
      intro j _
      rw [_root_.RHTower.Sieve.sum_stdAddChar_mul]
      simp [sub_eq_zero, eq_comm]
    _ = _ := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, intervalResidueMultiplicity, mul_comm]

/-- Integer interval pairs lying on the unit part of the modular-inverse graph. -/
def modularInverseRectangleCount
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) : ℕ :=
  ∑ u : (ZMod (M : ℕ))ˣ,
    intervalResidueMultiplicity M A L (u : ZMod (M : ℕ)) *
      intervalResidueMultiplicity M B H (c * (↑u⁻¹ : ZMod (M : ℕ)))

/-- Exact double Fourier completion, with no discarded endpoint or frequency term. -/
theorem modularInverseRectangleCount_fourier
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) :
    (M : ℂ) ^ 2 * (modularInverseRectangleCount M A L B H c : ℂ) =
      ∑ a : ZMod (M : ℕ), ∑ b : ZMod (M : ℕ),
        intervalAdditiveFourier M A L a * intervalAdditiveFourier M B H b *
          kloostermanSum (M : ℕ) a (b * c) := by
  rw [modularInverseRectangleCount, Nat.cast_sum, mul_sum]
  calc
    _ = ∑ u : (ZMod (M : ℕ))ˣ,
        ((M : ℂ) * (intervalResidueMultiplicity M A L (u : ZMod (M : ℕ)) : ℂ)) *
          ((M : ℂ) * (intervalResidueMultiplicity M B H
            (c * (↑u⁻¹ : ZMod (M : ℕ))) : ℂ)) := by
      apply sum_congr rfl
      intro u _
      push_cast
      ring
    _ = ∑ u : (ZMod (M : ℕ))ˣ,
        (∑ a : ZMod (M : ℕ), intervalAdditiveFourier M A L a *
          ZMod.stdAddChar (a * (u : ZMod (M : ℕ)))) *
        (∑ b : ZMod (M : ℕ), intervalAdditiveFourier M B H b *
          ZMod.stdAddChar (b * (c * (↑u⁻¹ : ZMod (M : ℕ))))) := by
      simp_rw [intervalResidueMultiplicity_fourier]
    _ = _ := by
      simp only [sum_mul]
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      rw [kloostermanSum, mul_sum]
      apply sum_congr rfl
      intro u _
      rw [kloostermanPhase,
        show a * (u : ZMod (M : ℕ)) + (b * c) * (↑u⁻¹ : ZMod (M : ℕ)) =
          a * (u : ZMod (M : ℕ)) + b * (c * (↑u⁻¹ : ZMod (M : ℕ))) by ring,
        AddChar.map_add_eq_mul]
      ring


/-! ## Divisor-weighted Fourier budgets -/

theorem intervalDivisorFourierMass_nonneg (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) (A : ℤ) (L : ℕ) :
    0 ≤ intervalDivisorFourierMass M d A L :=
  sum_nonneg (fun _ _ => norm_nonneg _)

/-- The actual gcd is one of the nonnegative common-divisor terms. -/
theorem residueGcd_le_divisor_sum (M : ℕ+) (a : ZMod (M : ℕ)) :
    (Nat.gcd (M : ℕ) a.val : ℝ) ≤
      ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors}, if d.val ∣ a.val then (d.val : ℝ) else 0 := by
  classical
  let g := Nat.gcd (M : ℕ) a.val
  have hg : g ∈ (M : ℕ).divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, M.pos.ne'⟩
  have h := single_le_sum
    (s := univ)
    (f := fun d : {d : ℕ // d ∈ (M : ℕ).divisors} =>
      if d.val ∣ a.val then (d.val : ℝ) else 0)
    (fun _ _ => by split_ifs <;> positivity)
    (mem_univ (⟨g, hg⟩ : {d : ℕ // d ∈ (M : ℕ).divisors}))
  dsimp [g] at h
  rw [if_pos (Nat.gcd_dvd_right (M : ℕ) a.val)] at h
  exact h

/-- Fourier mass with its exact gcd weight. -/
def intervalGcdFourierMass (M : ℕ+) (A : ℤ) (L : ℕ) : ℝ :=
  ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
    ‖intervalAdditiveFourier M A L a‖ * (Nat.gcd (M : ℕ) a.val : ℝ)

/-- Summing along divisor progressions costs one divisor count, including every nonprimitive frequency. -/
theorem intervalGcdFourierMass_le (M : ℕ+) (A : ℤ) (L : ℕ) :
    intervalGcdFourierMass M A L ≤
      ((M : ℕ).divisors.card : ℝ) * (M : ℝ) * (1 + Real.log (M : ℝ)) := by
  classical
  calc
    _ ≤ ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        ‖intervalAdditiveFourier M A L a‖ *
          ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
            if d.val ∣ a.val then (d.val : ℝ) else 0 := by
      apply sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (residueGcd_le_divisor_sum M a) (norm_nonneg _)
    _ = ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
        (d.val : ℝ) * intervalDivisorFourierMass M d A L := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [intervalDivisorFourierMass, mul_sum]
      simp only [sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0 <;> by_cases hd : d.val ∣ a.val <;> simp [ha, hd, mul_comm]
    _ ≤ ∑ _d : {d : ℕ // d ∈ (M : ℕ).divisors},
        (M : ℝ) * (1 + Real.log (M : ℝ)) := by
      apply sum_le_sum
      intro d _
      have hprod : (d.val : ℝ) * (modulusDivisorQuotient M d : ℝ) = (M : ℝ) := by
        exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors d.property)
      calc
        _ ≤ (d.val : ℝ) *
            ((modulusDivisorQuotient M d : ℝ) * (1 + Real.log (M : ℝ))) :=
          mul_le_mul_of_nonneg_left (intervalDivisorFourierMass_le M d A L)
            (Nat.cast_nonneg _)
        _ = _ := by rw [← mul_assoc, hprod]
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe, mul_assoc]

/-- The summable divisor weight is bounded independently of the modulus. -/
theorem sum_divisors_rpow_neg_five_thirds_le (M : ℕ+) :
    (∑ d ∈ (M : ℕ).divisors, (d : ℝ) ^ (-(5 / 3 : ℝ))) ≤ 3 := by
  have htail :
      (∑ j ∈ range ((M : ℕ) - 1), ((j + 2 : ℕ) : ℝ) ^ (-(5 / 3 : ℝ))) ≤ 3 / 2 := by
    have h := _root_.RHTower.sum_range_add_rpow_neg_le
      (c := (5 / 3 : ℝ)) (by norm_num) (M := 1) (by norm_num) ((M : ℕ) - 1)
    norm_num at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  calc
    _ ≤ ∑ d ∈ range ((M : ℕ) + 1), (d : ℝ) ^ (-(5 / 3 : ℝ)) := by
      apply sum_le_sum_of_subset_of_nonneg
        (fun d hd => mem_range.mpr (Nat.lt_succ_of_le (Nat.divisor_le hd)))
        (fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ 3 := by
      have hM : (M : ℕ) + 1 = ((M : ℕ) - 1) + 1 + 1 := by have := M.pos; omega
      rw [hM, sum_range_succ', sum_range_succ']
      norm_num only [Nat.cast_zero, Nat.zero_add, Nat.cast_one,
        Real.zero_rpow (by norm_num : -(5 / 3 : ℝ) ≠ 0), Real.one_rpow, add_zero]
      simpa only [Nat.add_assoc] using (show
        (∑ j ∈ range ((M : ℕ) - 1), ((j + 2 : ℕ) : ℝ) ^ (-(5 / 3 : ℝ))) + 1 ≤ 3 by linarith)


/-! ## The cubic estimate in completion scale -/

/-- Frequency-independent factor left after extracting the pair gcd. -/
def kloostermanCompletionScale (M : ℕ+) (c : ZMod (M : ℕ)) : ℝ :=
  8 * ((M : ℕ).divisors.card : ℝ) * (M : ℝ) ^ (2 / 3 : ℝ) *
    (Nat.gcd (M : ℕ) c.val : ℝ) ^ (1 / 3 : ℝ)

theorem kloostermanCompletionScale_nonneg (M : ℕ+) (c : ZMod (M : ℕ)) :
    0 ≤ kloostermanCompletionScale M c := by
  unfold kloostermanCompletionScale
  positivity

/-- Cube monotonicity converts the certified composite estimate into its exact completion scale. -/
theorem norm_kloostermanSum_le_completionScale
    (M : ℕ+) (a b c : ZMod (M : ℕ)) :
    ‖kloostermanSum (M : ℕ) a (b * c)‖ ≤
      kloostermanCompletionScale M c *
        (Nat.gcd (M : ℕ) (Nat.gcd a.val b.val) : ℝ) ^ (1 / 3 : ℝ) := by
  let g := Nat.gcd (M : ℕ) c.val
  let h := Nat.gcd (M : ℕ) (Nat.gcd a.val b.val)
  have hMpow : ((M : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (M : ℝ) ^ 2 := by
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ (M : ℝ))]
    norm_num
  have hgpow : ((g : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (g : ℝ) := by
    simpa only [one_div] using
      Real.rpow_inv_natCast_pow (n := 3) (Nat.cast_nonneg (α := ℝ) g) (by norm_num)
  have hhpow : ((h : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (h : ℝ) := by
    simpa only [one_div] using
      Real.rpow_inv_natCast_pow (n := 3) (Nat.cast_nonneg (α := ℝ) h) (by norm_num)
  have hcube : (kloostermanCompletionScale M c * (h : ℝ) ^ (1 / 3 : ℝ)) ^ 3 =
      512 * ((M : ℕ).divisors.card : ℝ) ^ 3 * (M : ℝ) ^ 2 * ((g : ℝ) * (h : ℝ)) := by
    change (8 * ((M : ℕ).divisors.card : ℝ) * (M : ℝ) ^ (2 / 3 : ℝ) *
      (g : ℝ) ^ (1 / 3 : ℝ) * (h : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = _
    simp only [mul_pow, hMpow, hgpow, hhpow]
    norm_num <;> ring
  have hfreq : (Nat.gcd (M : ℕ) (Nat.gcd a.val (b * c).val) : ℝ) ≤
      (g : ℝ) * (h : ℝ) := by
    exact_mod_cast residueFrequencyGcd_le M a b c
  have hbound := (norm_kloostermanSum_cube_le M a (b * c)).trans
    (mul_le_mul_of_nonneg_left hfreq (by positivity))
  rw [← hcube] at hbound
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (kloostermanCompletionScale_nonneg M c)
      (Real.rpow_nonneg (Nat.cast_nonneg h) _)) (by norm_num : 3 ≠ 0)).mp hbound

/-- The pair gcd is an actual member of the common-divisor sum. -/
theorem residuePairGcd_rpow_le_divisor_sum (M : ℕ+) (a b : ZMod (M : ℕ)) :
    (Nat.gcd (M : ℕ) (Nat.gcd a.val b.val) : ℝ) ^ (1 / 3 : ℝ) ≤
      ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
        if d.val ∣ a.val ∧ d.val ∣ b.val then (d.val : ℝ) ^ (1 / 3 : ℝ) else 0 := by
  classical
  let g := Nat.gcd (M : ℕ) (Nat.gcd a.val b.val)
  have hg : g ∈ (M : ℕ).divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, M.pos.ne'⟩
  have hga : g ∣ a.val := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hgb : g ∣ b.val := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have h := single_le_sum
    (s := univ)
    (f := fun d : {d : ℕ // d ∈ (M : ℕ).divisors} =>
      if d.val ∣ a.val ∧ d.val ∣ b.val then (d.val : ℝ) ^ (1 / 3 : ℝ) else 0)
    (fun _ _ => by split_ifs <;> positivity)
    (mem_univ (⟨g, hg⟩ : {d : ℕ // d ∈ (M : ℕ).divisors}))
  change (if g ∣ a.val ∧ g ∣ b.val then (g : ℝ) ^ (1 / 3 : ℝ) else 0) ≤ _ at h
  rw [if_pos (And.intro hga hgb)] at h
  exact h

/-- Two restricted Fourier masses leave the summable divisor exponent `−5/3`. -/
theorem divisorFrequencyScale_eq (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) :
    (d.val : ℝ) ^ (1 / 3 : ℝ) * (modulusDivisorQuotient M d : ℝ) ^ 2 =
      (M : ℝ) ^ 2 * (d.val : ℝ) ^ (-(5 / 3 : ℝ)) := by
  have hd : (0 : ℝ) < (d.val : ℝ) := by
    exact_mod_cast Nat.pos_of_mem_divisors d.property
  have hq : (modulusDivisorQuotient M d : ℝ) = (M : ℝ) / (d.val : ℝ) := by
    apply (eq_div_iff hd.ne').mpr
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors d.property)
  rw [hq, div_pow,
    show -(5 / 3 : ℝ) = (1 / 3 : ℝ) - (2 : ℕ) by norm_num,
    Real.rpow_sub_natCast hd.ne']
  ring


/-- Two interval transforms weighted by their actual common frequency gcd. -/
def intervalPairGcdFourierMass (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) : ℝ :=
  ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
    ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
      ‖intervalAdditiveFourier M A L a‖ * ‖intervalAdditiveFourier M B H b‖ *
        (Nat.gcd (M : ℕ) (Nat.gcd a.val b.val) : ℝ) ^ (1 / 3 : ℝ)

/-- The pair-gcd budget follows from two exact divisor-frequency restrictions. -/
theorem intervalPairGcdFourierMass_le (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) :
    intervalPairGcdFourierMass M A L B H ≤
      3 * (M : ℝ) ^ 2 * (1 + Real.log (M : ℝ)) ^ 2 := by
  classical
  have hλ : 0 ≤ 1 + Real.log (M : ℝ) := by
    have hM : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast M.pos
    have := Real.log_nonneg hM
    linarith
  have hdivsum :
      (∑ d : {d : ℕ // d ∈ (M : ℕ).divisors}, (d.val : ℝ) ^ (-(5 / 3 : ℝ))) ≤ 3 := by
    rw [← sum_subtype (M : ℕ).divisors (by simp)
      (fun d : ℕ => (d : ℝ) ^ (-(5 / 3 : ℝ)))]
    exact sum_divisors_rpow_neg_five_thirds_le M
  calc
    _ ≤ ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
          ‖intervalAdditiveFourier M A L a‖ * ‖intervalAdditiveFourier M B H b‖ *
            ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
              if d.val ∣ a.val ∧ d.val ∣ b.val then (d.val : ℝ) ^ (1 / 3 : ℝ) else 0 := by
      apply sum_le_sum
      intro a _
      apply sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (residuePairGcd_rpow_le_divisor_sum M a b)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
        (d.val : ℝ) ^ (1 / 3 : ℝ) *
          intervalDivisorFourierMass M d A L * intervalDivisorFourierMass M d B H := by
      simp only [mul_sum]
      simp_rw [sum_comm
        (s := univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0))
        (t := (univ : Finset {d : ℕ // d ∈ (M : ℕ).divisors}))]
      apply sum_congr rfl
      intro d _
      rw [mul_assoc, intervalDivisorFourierMass, intervalDivisorFourierMass,
        sum_mul_sum]
      simp only [mul_sum, sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0
      · simp [ha]
      by_cases hda : d.val ∣ a.val
      · simp only [ha, not_false_eq_true, hda, true_and, and_true, if_true]
        apply sum_congr rfl
        intro b _
        by_cases hb : b = 0 <;> by_cases hdb : d.val ∣ b.val <;>
          simp [hb, hdb, mul_assoc, mul_comm, mul_left_comm]
      · simp [ha, hda]
    _ ≤ ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
        (M : ℝ) ^ 2 * (1 + Real.log (M : ℝ)) ^ 2 *
          (d.val : ℝ) ^ (-(5 / 3 : ℝ)) := by
      apply sum_le_sum
      intro d _
      have hm := mul_le_mul
        (intervalDivisorFourierMass_le M d A L)
        (intervalDivisorFourierMass_le M d B H)
        (intervalDivisorFourierMass_nonneg M d B H)
        (mul_nonneg (by positivity : (0 : ℝ) ≤ (modulusDivisorQuotient M d : ℝ)) hλ)
      calc
        _ = (d.val : ℝ) ^ (1 / 3 : ℝ) *
            (intervalDivisorFourierMass M d A L * intervalDivisorFourierMass M d B H) := by ring
        _ ≤ (d.val : ℝ) ^ (1 / 3 : ℝ) *
            (((modulusDivisorQuotient M d : ℝ) * (1 + Real.log (M : ℝ))) *
              ((modulusDivisorQuotient M d : ℝ) * (1 + Real.log (M : ℝ)))) :=
          mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = ((d.val : ℝ) ^ (1 / 3 : ℝ) * (modulusDivisorQuotient M d : ℝ) ^ 2) *
            (1 + Real.log (M : ℝ)) ^ 2 := by ring
        _ = _ := by rw [divisorFrequencyScale_eq]; ring
    _ = (M : ℝ) ^ 2 * (1 + Real.log (M : ℝ)) ^ 2 *
        ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors}, (d.val : ℝ) ^ (-(5 / 3 : ℝ)) := by
      rw [mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hdivsum
        (mul_nonneg (sq_nonneg (M : ℝ)) (sq_nonneg (1 + Real.log (M : ℝ))))
      exact h.trans_eq (by ring)

end
end GaloisForLFunctions.Goldbach
