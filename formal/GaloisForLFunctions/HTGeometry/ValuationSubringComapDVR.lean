import GaloisForLFunctions.HTGeometry.LocalRamificationOrderLaw
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Nontrivial restrictions of discrete valuation rings

If a valuation subring is a discrete valuation ring, then its pullback along a field embedding is
again a discrete valuation ring as soon as the pulled-back valuation is nontrivial.  The proof uses
the least positive ambient discrete order and therefore does not require a finite field extension.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsDiscreteValuationRing

variable {F E : Type*} [Field F] [Field E]

/-- Canonical inclusion of a pulled-back valuation subring into the original valuation subring. -/
def valuationSubringComapInclusion (f : F →+* E) (B : ValuationSubring E) :
    B.comap f →+* B where
  toFun x := ⟨f x, x.property⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f (x : F) (y : F))
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f (x : F) (y : F))

theorem valuationSubringComapInclusion_injective (f : F →+* E) (B : ValuationSubring E) :
    Function.Injective (valuationSubringComapInclusion f B) := by
  intro x y hxy
  apply Subtype.ext
  exact f.injective (congrArg Subtype.val hxy)

/-- Pullback inclusion is local: an element whose image is a unit already has its inverse in the
pullback valuation ring. -/
instance valuationSubringComapInclusion_isLocalHom (f : F →+* E) (B : ValuationSubring E) :
    IsLocalHom (valuationSubringComapInclusion f B) where
  map_nonunit a ha := by
    have hval : B.valuation (f (a : F)) = 1 :=
      (B.valuation_eq_one_iff (valuationSubringComapInclusion f B a)).mp ha
    have hinv : f (a : F)⁻¹ ∈ B := by
      rw [← B.valuation_le_one_iff, map_inv₀, map_inv₀, hval, inv_one]
    rw [isUnit_iff_exists_inv]
    refine ⟨⟨(a : F)⁻¹, hinv⟩, Subtype.ext ?_⟩
    exact mul_inv_cancel₀ (by
      intro ha0
      simp [ha0] at hval)

/-- A proper valuation subring contains a nonzero nonunit. -/
private theorem valuationSubring_exists_nonzero_nonunit (O : ValuationSubring F) (hne : O ≠ ⊤) :
    ∃ a : O, a ≠ 0 ∧ ¬IsUnit a := by
  obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  have hx0 : x ≠ 0 := fun hx0 => hx (hx0 ▸ O.zero_mem)
  have hxinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
  let a : O := ⟨x⁻¹, hxinv⟩
  have ha0 : a ≠ 0 := by
    intro ha
    exact (inv_ne_zero hx0) (congrArg Subtype.val ha)
  refine ⟨a, ha0, ?_⟩
  intro ha
  have haval : O.valuation (x⁻¹) = 1 := (O.valuation_eq_one_iff a).mp ha
  apply hx
  rw [← O.valuation_le_one_iff, ← inv_inv x, map_inv₀, haval, inv_one]

/-- The discrete order of a nonzero nonunit is positive. -/
private theorem natOrd_pos_of_not_isUnit
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {a : A} (ha0 : a ≠ 0) (ha : ¬IsUnit a) : 0 < natOrd A a := by
  apply Nat.pos_of_ne_zero
  intro hzero
  apply ha
  rw [← addVal_eq_zero_iff, natOrd_spec ha0, hzero]
  rfl

/-- Natural discrete order of a nonzero power. -/
private theorem natOrd_pow_of_ne_zero
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {a : A} (ha0 : a ≠ 0) : ∀ n : ℕ, natOrd A (a ^ n) = n * natOrd A a := by
  intro n
  induction n with
  | zero =>
      have hone : natOrd A 1 = 0 := by
        apply ENat.coe_inj.mp
        rw [← natOrd_spec one_ne_zero, AddValuation.map_one]
        rfl
      simp [hone]
  | succ n ih =>
      rw [pow_succ, natOrd_mul (pow_ne_zero n ha0) ha0, ih, Nat.succ_mul]

/-- A nontrivial pullback of a discrete valuation ring along a field embedding is a discrete
valuation ring. -/
theorem valuationSubringComap_isDiscreteValuationRing
    (f : F →+* E) (B : ValuationSubring E) [IsDiscreteValuationRing B]
    (hne : B.comap f ≠ ⊤) : IsDiscreteValuationRing (B.comap f) := by
  classical
  let O := B.comap f
  let ψ := valuationSubringComapInclusion f B
  have hψinj : Function.Injective ψ := valuationSubringComapInclusion_injective f B
  obtain ⟨w, hw0, hwu⟩ := valuationSubring_exists_nonzero_nonunit O hne
  have hψw0 : ψ w ≠ 0 := fun h => hw0 (hψinj (by simpa using h))
  have hψwu : ¬IsUnit (ψ w) := by simpa only [isUnit_map_iff] using hwu
  let P : ℕ → Prop := fun d =>
    ∃ a : O, a ≠ 0 ∧ ¬IsUnit a ∧ natOrd B (ψ a) = d
  have hP : ∃ d, P d := ⟨natOrd B (ψ w), w, hw0, hwu, rfl⟩
  let d := Nat.find hP
  obtain ⟨π, hπ0, hπu, hπord⟩ := Nat.find_spec hP
  have hπord' : natOrd B (ψ π) = d := by simpa [d] using hπord
  have hψπ0 : ψ π ≠ 0 := fun h => hπ0 (hψinj (by simpa using h))
  have hψπu : ¬IsUnit (ψ π) := by simpa only [isUnit_map_iff] using hπu
  have hdpos : 0 < d := by
    rw [← hπord']
    exact natOrd_pos_of_not_isUnit hψπ0 hψπu
  have hminimal {a : O} (ha0 : a ≠ 0) (hau : ¬IsUnit a) :
      d ≤ natOrd B (ψ a) := by
    exact Nat.find_min' hP ⟨a, ha0, hau, rfl⟩
  have hπirr : Irreducible π := by
    rw [irreducible_iff]
    refine ⟨hπu, ?_⟩
    intro a b hab
    by_contra habu
    have habu := not_or.mp habu
    have ha0 : a ≠ 0 := fun ha => hπ0 (by simp [hab, ha])
    have hb0 : b ≠ 0 := fun hb => hπ0 (by simp [hab, hb])
    have hψa0 : ψ a ≠ 0 := fun h => ha0 (hψinj (by simpa using h))
    have hψb0 : ψ b ≠ 0 := fun h => hb0 (hψinj (by simpa using h))
    have hord : d = natOrd B (ψ a) + natOrd B (ψ b) := by
      rw [← hπord', hab, map_mul, natOrd_mul hψa0 hψb0]
    have hamin := hminimal ha0 habu.1
    have hbmin := hminimal hb0 habu.2
    omega
  apply ofHasUnitMulPowIrreducibleFactorization
  refine ⟨π, hπirr, ?_⟩
  intro x hx0
  have hψx0 : ψ x ≠ 0 := fun h => hx0 (hψinj (by simpa using h))
  let q := natOrd B (ψ x) / d
  let r := natOrd B (ψ x) % d
  have hrlt : r < d := Nat.mod_lt _ hdpos
  have hqdvd : ψ (π ^ q) ∣ ψ x := by
    rw [← addVal_le_iff_dvd]
    rw [map_pow, natOrd_spec (pow_ne_zero q hψπ0), natOrd_spec hψx0]
    apply ENat.coe_le_coe.mpr
    rw [natOrd_pow_of_ne_zero hψπ0, hπord']
    simpa [q, Nat.mul_comm] using Nat.mul_div_le (natOrd B (ψ x)) d
  obtain ⟨c, hc⟩ := hqdvd
  let zF : F := (x : F) / (π : F) ^ q
  have hπpowF0 : (π : F) ^ q ≠ 0 :=
    pow_ne_zero q (Subtype.coe_injective.ne hπ0)
  have hπpowE0 : f ((π : F) ^ q) ≠ 0 := by
    intro h
    apply hπpowF0
    apply f.injective
    simpa using h
  have hcE : f (x : F) = f ((π : F) ^ q) * (c : E) := by
    exact congrArg Subtype.val hc
  have hzmap : f zF = (c : E) := by
    apply mul_left_cancel₀ hπpowE0
    rw [show f zF = f (x : F) / f ((π : F) ^ q) by simp [zF],
      mul_div_cancel₀ (f (x : F)) hπpowE0, hcE]
  have hzmem : zF ∈ O := by
    change f zF ∈ B
    rw [hzmap]
    exact c.property
  let z : O := ⟨zF, hzmem⟩
  have hxsplit : π ^ q * z = x := by
    apply Subtype.ext
    change (π : F) ^ q * zF = (x : F)
    exact mul_div_cancel₀ (x : F) hπpowF0
  have hz0 : z ≠ 0 := by
    intro hz
    apply hx0
    rw [← hxsplit, hz, mul_zero]
  have hψz0 : ψ z ≠ 0 := by
    intro hz
    apply hz0
    apply hψinj
    simpa using hz
  have hzord : natOrd B (ψ z) = r := by
    have htotal : natOrd B (ψ x) = d * q + r := by
      simpa [q, r] using (Nat.div_add_mod (natOrd B (ψ x)) d).symm
    have hsplit : natOrd B (ψ x) = d * q + natOrd B (ψ z) := by
      rw [← hxsplit, map_mul, map_pow,
        natOrd_mul (pow_ne_zero q hψπ0) hψz0,
        natOrd_pow_of_ne_zero hψπ0, hπord']
      simp [Nat.mul_comm]
    omega
  have hzu : IsUnit z := by
    by_contra hzu
    have := hminimal (fun hz0 => hψz0 (by simp [hz0])) hzu
    rw [hzord] at this
    omega
  refine ⟨q, (associated_mul_unit_right (π ^ q) z hzu).trans ?_⟩
  exact Associated.of_eq hxsplit

end

end GaloisForLFunctions.HTGeometry
