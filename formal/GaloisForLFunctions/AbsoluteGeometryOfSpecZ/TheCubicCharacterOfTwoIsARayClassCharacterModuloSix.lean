import GaloisForLFunctions.HeckeLFunctions.ResidueCharactersTrivialOnUnitsAreHeckeCharacters
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicPhaseLivesModuloTwo
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicPrimaryIdealGenerators

/-!
# The cubic character of two is a ray class character modulo six

Let `O = ℤ[ω]` be the Eisenstein integers, `λ = ω − 1`, and for an ideal `𝔞` prime to `λ` let
`π_𝔞` be its primary generator (`π_𝔞 ≡ 1 mod λ²`). Read `π_𝔞 mod 2` in the cubic roots of unity
through the cubic residue character of the inert prime `2`:

  `χ(𝔞) = (π_𝔞 mod 2)`  (`twoCubicValue`).

* `χ` is multiplicative, trivial on units, nonzero exactly on the ideals prime to `6`, and on
  principal ideals `(α)` a function of `α mod 6` (`twoCubicOf_eq_of_six_dvd`).
* It is the ray class character `cubicTwoHecke` modulo `6` (`heckeValue_cubicTwoHecke`), of
  conductor exactly `6` (`heckeFiniteConductor_cubicTwoHecke`): it is non-trivial on
  `1 + 3ω ≡ 1 (mod 3)` and on `1 + 2λ ≡ 1 (mod 2λ)`.
* **Cubic reciprocity at `2`.** At every prime `𝔭 ∤ 6`, `χ(𝔭)` is the cubic residue symbol of `2`
  modulo `𝔭` (`twoCubicValue_prime`).
-/

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CubeRootsOfTwo

open MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein HeckeLFunctions

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-! ### Arithmetic of `2` and `λ` -/

theorem lambda_prime : Prime lambda := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

theorem omega_sq : omega ^ 2 = -omega - 1 := by
  have hrel : omega ^ 2 + omega + 1 = 0 := by
    simpa only [IsCyclotomicExtension.Rat.Three.coe_eta, omega] using
      (IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
        (IsCyclotomicExtension.zeta_spec 3 ℚ K))
  linear_combination hrel

theorem lambda_sq : lambda ^ 2 = -3 * omega := by
  rw [lambda]
  linear_combination omega_sq

theorem omega_isUnit : IsUnit omega := omega_primitive.isUnit (by decide)

theorem two_mem_cubicTwoIdeal : (2 : O) ∈ cubicTwoIdeal := by
  rw [cubicTwoIdeal, Ideal.span_singleton_neg]
  exact Ideal.subset_span rfl

theorem mem_cubicTwoIdeal_iff (x : O) : x ∈ cubicTwoIdeal ↔ (2 : O) ∣ x := by
  rw [cubicTwoIdeal, Ideal.span_singleton_neg, Ideal.mem_span_singleton]

theorem two_prime : Prime (2 : O) := by
  have h := (Ideal.span_singleton_prime (by norm_num : (-2 : O) ≠ 0)).mp
    (cubicTwoIdeal_isMaximal.isPrime)
  simpa using h.neg

/-- `6 = 2 · λ² · (−ω²)`. -/
theorem six_eq : (6 : O) = 2 * lambda ^ 2 * (-omega ^ 2) := by
  rw [lambda_sq]
  have h3 : omega ^ 3 = 1 := omega_primitive.pow_eq_one
  linear_combination (-6 : O) * h3

theorem neg_omega_sq_isUnit : IsUnit (-omega ^ 2) := (omega_isUnit.pow 2).neg

/-- An element prime to `λ` and to `2` is prime to `6`. -/
theorem isCoprime_six {a : O} (hl : ¬ lambda ∣ a) (h2 : ¬ (2 : O) ∣ a) : IsCoprime a 6 := by
  have h1 : IsCoprime a (2 * lambda ^ 2) :=
    IsCoprime.mul_right ((two_prime.irreducible.coprime_iff_not_dvd.mpr h2).symm)
      ((lambda_prime.irreducible.coprime_iff_not_dvd.mpr hl).symm.pow_right)
  rw [six_eq]
  exact (isCoprime_mul_unit_right_right neg_omega_sq_isUnit a _).mpr h1

/-- An element whose residue modulo `6` is a unit is prime to `λ` and to `2`. -/
theorem not_dvd_of_isUnit_mk {a : O} (ha : IsUnit (Ideal.Quotient.mk (Ideal.span {(6 : O)}) a)) :
    ¬ lambda ∣ a ∧ ¬ (2 : O) ∣ a := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective b
  rw [← hc, ← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at hb
  have hl6 : lambda ∣ (6 : O) := by
    rw [six_eq]
    exact ⟨2 * lambda * (-omega ^ 2), by ring⟩
  have h26 : (2 : O) ∣ 6 := ⟨3, by norm_num⟩
  constructor
  · intro hl
    have h1 : lambda ∣ (1 : O) := by
      have := dvd_sub (hl.mul_right c) (hl6.trans hb)
      simpa using this
    exact lambda_prime.not_unit (isUnit_of_dvd_one h1)
  · intro h2
    have h1 : (2 : O) ∣ 1 := by
      have := dvd_sub (h2.mul_right c) (h26.trans hb)
      simpa using this
    exact two_prime.not_unit (isUnit_of_dvd_one h1)

/-! ### The character on ideals -/

/-- The cubic residue character modulo the inert prime `2`. -/
abbrev twoChar : MulChar (O ⧸ cubicTwoIdeal) O := cubicChar cubicTwoIdeal cubicTwoIdeal_good

/-- **The cubic character of `2` on ideals**: `𝔞 ↦ (π_𝔞 mod 2)`, `π_𝔞` the primary generator. -/
def twoCubicValue (I : Ideal O) : O :=
  twoChar (Ideal.Quotient.mk cubicTwoIdeal (primaryIdealGenerator I))

theorem twoCubicValue_mul (I J : Ideal O) :
    twoCubicValue (I * J) = twoCubicValue I * twoCubicValue J := by
  simp only [twoCubicValue, primaryIdealGenerator_mul, map_mul]

theorem twoCubicValue_top : twoCubicValue ⊤ = 1 := by
  rw [twoCubicValue, ← Ideal.one_eq_top, primaryIdealGenerator_one, map_one, MulChar.map_one]

theorem twoCubicValue_bot : twoCubicValue ⊥ = 0 := by
  rw [twoCubicValue, primaryIdealGenerator_bot, map_zero, MulChar.map_zero]

/-- The residue field at `2` has four elements. -/
theorem card_quot_cubicTwoIdeal : Nat.card (O ⧸ cubicTwoIdeal) = 4 := by
  rw [← cubicTwoIdeal_absNorm, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- On the residue field `𝔽₄` the cubic character is the identity read in `O`. -/
theorem mk_twoChar (x : O ⧸ cubicTwoIdeal) :
    Ideal.Quotient.mk cubicTwoIdeal (twoChar x) = x := by
  rw [cubicChar_reduce, card_quot_cubicTwoIdeal]
  norm_num

/-- `χ(2 ∤ x) = 1` iff `x ≡ 1 (mod 2)`. -/
theorem twoChar_mk_eq_one_iff (x : O) :
    twoChar (Ideal.Quotient.mk cubicTwoIdeal x) = 1 ↔ (2 : O) ∣ x - 1 := by
  constructor
  · intro h
    have h' := mk_twoChar (Ideal.Quotient.mk cubicTwoIdeal x)
    rw [h, map_one, eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk cubicTwoIdeal),
      ← map_sub, Ideal.Quotient.eq_zero_iff_mem, mem_cubicTwoIdeal_iff] at h'
    exact h'
  · intro h
    have h1 : Ideal.Quotient.mk cubicTwoIdeal x = 1 := by
      rw [← map_one (Ideal.Quotient.mk cubicTwoIdeal), Ideal.Quotient.eq, mem_cubicTwoIdeal_iff]
      exact h
    rw [h1, MulChar.map_one]

/-- The value on a primary element is its class modulo `2`. -/
theorem twoCubicValue_span_primary {a : O} (ha : lambda ^ 2 ∣ a - 1) :
    twoCubicValue (Ideal.span {a}) = twoChar (Ideal.Quotient.mk cubicTwoIdeal a) := by
  rw [twoCubicValue, primaryIdealGenerator_span a (primary_ne_zero a ha) ha]

/-- The value on a principal ideal. -/
def twoCubicOf (a : O) : O := twoCubicValue (Ideal.span {a})

theorem twoCubicOf_mul (a b : O) : twoCubicOf (a * b) = twoCubicOf a * twoCubicOf b := by
  rw [twoCubicOf, twoCubicOf, twoCubicOf, ← Ideal.span_singleton_mul_span_singleton,
    twoCubicValue_mul]

theorem twoCubicOf_unit (u : Oˣ) : twoCubicOf u = 1 := by
  rw [twoCubicOf, Ideal.span_singleton_eq_top.mpr u.isUnit, twoCubicValue_top]

/-- **Periodicity modulo six.** -/
theorem twoCubicOf_eq_of_six_dvd {a b : O} (ha : ¬ lambda ∣ a) (hab : (6 : O) ∣ a - b) :
    twoCubicOf a = twoCubicOf b := by
  have hl6 : lambda ^ 2 ∣ (6 : O) := by
    rw [six_eq]
    exact ⟨2 * (-omega ^ 2), by ring⟩
  have h26 : (2 : O) ∣ 6 := ⟨3, by norm_num⟩
  have hb : ¬ lambda ∣ b := by
    intro hb
    apply ha
    have := dvd_add ((dvd_pow_self lambda two_ne_zero).trans (hl6.trans hab)) hb
    simpa using this
  have hga := (primaryIdealGenerator_span_ne_zero_iff a).mpr ha
  have hgb := (primaryIdealGenerator_span_ne_zero_iff b).mpr hb
  obtain ⟨hsa, hpa⟩ := primaryIdealGenerator_spec _ hga
  obtain ⟨hsb, hpb⟩ := primaryIdealGenerator_spec _ hgb
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hsa
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hsb
  set g := primaryIdealGenerator (Ideal.span {a})
  set h := primaryIdealGenerator (Ideal.span {b})
  -- the two normalizing units agree modulo `λ²`, hence are equal
  have huv : (u : O) = v := by
    have hdiff : lambda ^ 2 ∣ (u : O) - v := by
      have e : (u : O) - v = (a - b) - (g - 1) * u + (h - 1) * v := by
        rw [← hu, ← hv]; ring
      rw [e]
      exact dvd_add (dvd_sub (hl6.trans hab) (hpa.mul_right _)) (hpb.mul_right _)
    have h1 : lambda ^ 2 ∣ ((u * v⁻¹ : Oˣ) : O) - 1 := by
      have e : ((u * v⁻¹ : Oˣ) : O) - 1 = ((u : O) - v) * (v⁻¹ : Oˣ) := by
        simp only [Units.val_mul, sub_mul, Units.mul_inv]
      rw [e]
      exact hdiff.mul_right _
    have h2 := primary_unit_eq_one _ h1
    have h3 : u * v⁻¹ = 1 := Units.ext h2
    rw [mul_inv_eq_one] at h3
    rw [h3]
  have huv' : u = v := Units.ext huv
  subst huv'
  have hgh : (2 : O) ∣ g - h := by
    have e : g - h = (a - b) * (u⁻¹ : Oˣ) := by
      have hu' : g = a * (u⁻¹ : Oˣ) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
      have hv' : h = b * (u⁻¹ : Oˣ) := by rw [← hv, mul_assoc, Units.mul_inv, mul_one]
      rw [hu', hv']; ring
    rw [e]
    exact (h26.trans hab).mul_right _
  rw [twoCubicOf, twoCubicOf, twoCubicValue, twoCubicValue]
  congr 1
  rw [Ideal.Quotient.eq, mem_cubicTwoIdeal_iff]
  exact hgh

theorem isUnit_twoCubicOf {a : O} (hl : ¬ lambda ∣ a) (h2 : ¬ (2 : O) ∣ a) :
    IsUnit (twoCubicOf a) := by
  have hg := (primaryIdealGenerator_span_ne_zero_iff a).mpr hl
  obtain ⟨hs, -⟩ := primaryIdealGenerator_spec _ hg
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  have hmk : IsUnit (Ideal.Quotient.mk cubicTwoIdeal (primaryIdealGenerator (Ideal.span {a}))) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem, mem_cubicTwoIdeal_iff]
    intro hd
    exact h2 (hu ▸ hd.mul_right _)
  exact hmk.map twoChar

/-- `χ(𝔞) ≠ 0` iff `𝔞` is prime to `6`. -/
theorem twoCubicValue_ne_zero_iff (I : Ideal O) :
    twoCubicValue I ≠ 0 ↔ I ⊔ Ideal.span {(6 : O)} = ⊤ := by
  obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  change twoCubicOf a ≠ 0 ↔ _
  constructor
  · intro h
    have hl : ¬ lambda ∣ a := by
      intro hl
      apply h
      rw [twoCubicOf, twoCubicValue,
        (not_ne_iff.mp (mt (primaryIdealGenerator_span_ne_zero_iff a).mp (not_not.mpr hl))),
        map_zero, MulChar.map_zero]
    have h2 : ¬ (2 : O) ∣ a := by
      intro h2
      apply h
      have hg := (primaryIdealGenerator_span_ne_zero_iff a).mpr hl
      obtain ⟨hs, -⟩ := primaryIdealGenerator_spec _ hg
      obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.symm
      rw [twoCubicOf, twoCubicValue]
      have hz : Ideal.Quotient.mk cubicTwoIdeal (primaryIdealGenerator (Ideal.span {a})) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, mem_cubicTwoIdeal_iff, ← hu]
        exact h2.mul_right _
      rw [hz, MulChar.map_zero]
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact isCoprime_six hl h2
  · intro h
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff] at h
    have hmk : IsUnit (Ideal.Quotient.mk (Ideal.span {(6 : O)}) a) := by
      obtain ⟨x, y, hxy⟩ := h
      refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk _ x, ?_⟩
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨-y, by linear_combination hxy⟩
    obtain ⟨hl, h2⟩ := not_dvd_of_isUnit_mk hmk
    exact (isUnit_twoCubicOf hl h2).ne_zero


/-- On an ideal `(n)` with `n` prime to `6` the character is `1`: `±n` is primary and odd. -/
theorem twoCubicValue_natCast {n : ℕ} (h2 : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    twoCubicValue (Ideal.span {(n : O)}) = 1 := by
  have hl6 : lambda ^ 2 ∣ (6 : O) := by
    rw [six_eq]
    exact ⟨2 * (-omega ^ 2), by ring⟩
  have h26 : (2 : O) ∣ 6 := ⟨3, by norm_num⟩
  have hmod : n % 6 = 1 ∨ n % 6 = 5 := by omega
  rcases hmod with h | h
  · have hn : (n : O) - 1 = 6 * ((n / 6 : ℕ) : O) := by
      have : n = 6 * (n / 6) + 1 := by omega
      conv_lhs => rw [this]
      push_cast; ring
    rw [twoCubicValue_span_primary (by rw [hn]; exact hl6.mul_right _),
      twoChar_mk_eq_one_iff, hn]
    exact h26.mul_right _
  · have hn : -(n : O) - 1 = 6 * (-((n / 6 : ℕ) : O) - 1) := by
      have : n = 6 * (n / 6) + 5 := by omega
      conv_lhs => rw [this]
      push_cast; ring
    rw [← Ideal.span_singleton_neg, twoCubicValue_span_primary (by rw [hn]; exact hl6.mul_right _),
      twoChar_mk_eq_one_iff, hn]
    exact h26.mul_right _

/-- **Cubic reciprocity at `2`.** At a prime `𝔭 ∤ 6`, `χ(𝔭)` is the cubic residue symbol of `2`. -/
theorem twoCubicValue_prime (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (hchar : ringChar (O ⧸ P) ≠ 2) :
    twoCubicValue P = cubicChar P hg (Ideal.Quotient.mk P 2) := by
  have hspec := primaryGenerator_spec P hg
  have hgen : primaryIdealGenerator P = primaryGenerator P hg := by
    conv_lhs => rw [hspec.1]
    exact primaryIdealGenerator_span _ (primary_ne_zero _ hspec.2) hspec.2
  rw [twoCubicValue, hgen]
  have hrec := cubic_reciprocity_distinct_residue_char P cubicTwoIdeal hg cubicTwoIdeal_good
    (by rw [cubicTwoIdeal_residue_char]; exact Ne.symm hchar) (primaryGenerator P hg) (-2)
    hspec.1 rfl hspec.2 neg_two_primary
  have hneg : Ideal.Quotient.mk P (-2 : O) = -1 * Ideal.Quotient.mk P 2 := by
    rw [map_neg, neg_one_mul]
  rw [← hrec, hneg, map_mul, cubicChar_neg_one, one_mul]

/-! ### The ray class character modulo six -/

/-- The modulus `6` of `ℚ(ω)`; the field has no real place. -/
abbrev sixModulus : Modulus K where
  fin := Ideal.span {(6 : O)}
  fin_ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    norm_num
  inf := ∅

/-- A representative in `O` of a residue modulo `6`. -/
def sixLift (x : O ⧸ Ideal.span {(6 : O)}) : O := (Ideal.Quotient.mk_surjective x).choose

theorem mk_sixLift (x : O ⧸ Ideal.span {(6 : O)}) : Ideal.Quotient.mk _ (sixLift x) = x :=
  (Ideal.Quotient.mk_surjective x).choose_spec

theorem six_dvd_sub_of_mk_eq {a b : O}
    (h : Ideal.Quotient.mk (Ideal.span {(6 : O)}) a = Ideal.Quotient.mk _ b) : (6 : O) ∣ a - b :=
  Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)

theorem sixLift_good (x : (O ⧸ Ideal.span {(6 : O)})ˣ) :
    ¬ lambda ∣ sixLift x ∧ ¬ (2 : O) ∣ sixLift x :=
  not_dvd_of_isUnit_mk (by rw [mk_sixLift]; exact x.isUnit)

theorem twoCubicOf_one : twoCubicOf 1 = 1 := by
  simpa using twoCubicOf_unit 1

/-- The character on the units modulo `6`, as a function. -/
def sixResidueFun (x : (O ⧸ Ideal.span {(6 : O)})ˣ) : Oˣ :=
  (isUnit_twoCubicOf (sixLift_good x).1 (sixLift_good x).2).unit

theorem coe_sixResidueFun (x : (O ⧸ Ideal.span {(6 : O)})ˣ) :
    (sixResidueFun x : O) = twoCubicOf (sixLift x) := IsUnit.unit_spec _

/-- The value at any representative. -/
theorem sixResidueFun_eq {x : (O ⧸ Ideal.span {(6 : O)})ˣ} {a : O}
    (h : (x : O ⧸ Ideal.span {(6 : O)}) = Ideal.Quotient.mk _ a) :
    (sixResidueFun x : O) = twoCubicOf a := by
  rw [coe_sixResidueFun]
  exact twoCubicOf_eq_of_six_dvd (sixLift_good x).1 (six_dvd_sub_of_mk_eq (by rw [mk_sixLift, h]))

/-- The character on the units modulo `6`, with values in the cubic roots of unity of `O`. -/
def sixResidueChar : (O ⧸ Ideal.span {(6 : O)})ˣ →* Oˣ where
  toFun := sixResidueFun
  map_one' := Units.ext (by
    rw [sixResidueFun_eq (a := 1) (by rw [Units.val_one, map_one]), Units.val_one, twoCubicOf_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mul, sixResidueFun_eq (a := sixLift x * sixLift y)
      (by rw [Units.val_mul, map_mul, mk_sixLift, mk_sixLift]), twoCubicOf_mul,
      coe_sixResidueFun, coe_sixResidueFun])

theorem coe_sixResidueChar (x : (O ⧸ Ideal.span {(6 : O)})ˣ) :
    (sixResidueChar x : O) = twoCubicOf (sixLift x) := coe_sixResidueFun x

/-- The value on the residue of an element prime to `6`. -/
theorem coe_sixResidueChar_mk {a : O} (ha : IsUnit (Ideal.Quotient.mk (Ideal.span {(6 : O)}) a)) :
    (sixResidueChar ha.unit : O) = twoCubicOf a :=
  sixResidueFun_eq (IsUnit.unit_spec ha)

/-- The residue character with trivial signs, valued in `ℂˣ`. -/
def sixResidueComplex : (O ⧸ sixModulus.fin)ˣ × (sixModulus.inf → ℤˣ) →* ℂˣ :=
  (Units.map ringComplex.toMonoidHom).comp (sixResidueChar.comp (MonoidHom.fst _ _))

theorem sixResidueComplex_globalUnit (u : (𝓞 K)ˣ) :
    sixResidueComplex (rayHom sixModulus (globalUnitPrimeTo sixModulus u)) = 1 := by
  ext
  change ringComplex (sixResidueChar (reduce sixModulus (globalUnitPrimeTo sixModulus u)) : O) = 1
  rw [reduce_globalUnit, coe_sixResidueChar]
  rw [twoCubicOf_eq_of_six_dvd (sixLift_good _).1 (b := (u : O))
    (six_dvd_sub_of_mk_eq (by rw [mk_sixLift]; rfl)), twoCubicOf_unit, map_one]

/-- **The cubic character of `2` as a ray class character modulo `6`.** -/
def cubicTwoHecke : HeckeCharacter sixModulus :=
  heckeOfResidue sixModulus sixResidueComplex sixResidueComplex_globalUnit

/-- **Values on integral ideals**: `χ(𝔞) = (π_𝔞 mod 2)`, and `0` on ideals not prime to `6`. -/
theorem heckeValue_cubicTwoHecke (I : Ideal O) :
    heckeValue sixModulus cubicTwoHecke I = ringComplex (twoCubicValue I) := by
  by_cases hI : I = ⊥
  · subst hI
    rw [heckeValue_of_not_mem sixModulus cubicTwoHecke (fun h => h.1 rfl), twoCubicValue_bot,
      map_zero]
  by_cases hm : idealUnit hI ∈ idealGroup sixModulus
  · have hcop := (idealUnit_mem_idealGroup_iff sixModulus hI).mp hm
    obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
    have hIa : I = Ideal.span {a} := ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hI (by rw [hIa, Ideal.span_singleton_eq_bot])
    have hγ0 : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha0
    have hγ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v.asIdeal ∣ sixModulus.fin →
        a ∉ v.asIdeal := by
      intro v hv hav
      apply v.isPrime.ne_top
      rw [eq_top_iff, ← hcop]
      refine sup_le ?_ (Ideal.dvd_iff_le.mp hv)
      rw [hIa, Ideal.span_le, Set.singleton_subset_iff]
      exact hav
    let α : primeToUnits sixModulus := ⟨Units.mk0 _ hγ0, mk0_mem_primeToUnits sixModulus hγ0 hγ⟩
    have hcls : rayClass sixModulus ⟨idealUnit hI, hm⟩ = rayClassOfElt sixModulus α := by
      change rayClass sixModulus ⟨idealUnit hI, hm⟩ = rayClass sixModulus ⟨_, _⟩
      congr 1
      apply Subtype.ext
      apply Units.ext
      rw [coe_idealUnit]
      change (I : FractionalIdeal (𝓞 K)⁰ K) =
        ((toPrincipalIdeal (𝓞 K) K (Units.mk0 _ hγ0) : FractionalIdeal (𝓞 K)⁰ K))
      rw [coe_toPrincipalIdeal, Units.val_mk0, hIa, FractionalIdeal.coeIdeal_span_singleton]
    rw [heckeValue_of_mem sixModulus cubicTwoHecke hI hm, hcls, cubicTwoHecke,
      heckeOfResidue_rayClassOfElt, rayHom_algebraMap sixModulus hγ0 hγ]
    change ringComplex (sixResidueChar (unitMod sixModulus hγ) : O) = _
    have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {(6 : O)}) a) := (unitMod sixModulus hγ).isUnit
    have he : unitMod sixModulus hγ = hu.unit := Units.ext rfl
    rw [he, coe_sixResidueChar_mk hu, twoCubicOf, ← hIa]
  · rw [heckeValue_of_not_mem sixModulus cubicTwoHecke (fun ⟨_, h⟩ => hm h)]
    have h0 : twoCubicValue I = 0 := by
      by_contra hne
      exact hm ((idealUnit_mem_idealGroup_iff sixModulus hI).mpr
        ((twoCubicValue_ne_zero_iff I).mp hne))
    rw [h0, map_zero]

/-- The finite residue weight on a unit residue. -/
theorem finiteHeckeWeight_cubicTwoHecke {a : O}
    (ha : IsUnit (Ideal.Quotient.mk (Ideal.span {(6 : O)}) a)) :
    finiteHeckeWeight sixModulus cubicTwoHecke (Ideal.Quotient.mk _ a) =
      ringComplex (twoCubicOf a) := by
  have h := finiteHeckeWeight_unit sixModulus cubicTwoHecke ha.unit
  rw [IsUnit.unit_spec] at h
  rw [h, cubicTwoHecke, finiteResidueCharacter_heckeOfResidue]
  change ringComplex (sixResidueChar ha.unit : O) = _
  rw [coe_sixResidueChar_mk ha]

/-! ### Primitivity -/

theorem one_add_omega_eq : 1 + omega = -omega ^ 2 := by
  rw [omega_sq]; ring

theorem not_two_dvd_one_add_omega : ¬ (2 : O) ∣ 1 + omega := by
  rw [one_add_omega_eq]
  exact fun h => two_prime.not_unit (isUnit_of_dvd_unit h neg_omega_sq_isUnit)

theorem isUnit_mk_six {a : O} (hl : ¬ lambda ∣ a) (h2 : ¬ (2 : O) ∣ a) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(6 : O)}) a) := by
  obtain ⟨x, y, hxy⟩ := isCoprime_six hl h2
  refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk _ x, ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨-y, by linear_combination hxy⟩

/-- `1 + 3ω ≡ 1 (mod 3)` but `χ(1 + 3ω) ≠ 1`. -/
theorem twoCubicOf_one_add_three_omega_ne_one : twoCubicOf (1 + 3 * omega) ≠ 1 := by
  have hp : lambda ^ 2 ∣ (1 + 3 * omega) - 1 := by
    rw [lambda_sq]; exact ⟨-1, by ring⟩
  rw [twoCubicOf, twoCubicValue_span_primary hp, Ne, twoChar_mk_eq_one_iff]
  intro h
  have hω : (2 : O) ∣ omega := by
    have e : omega = (1 + 3 * omega - 1) - 2 * omega := by ring
    rw [e]
    exact dvd_sub h (dvd_mul_right _ _)
  exact two_prime.not_unit (isUnit_of_dvd_unit hω omega_isUnit)

theorem good_one_add_three_omega :
    ¬ lambda ∣ 1 + 3 * omega ∧ ¬ (2 : O) ∣ 1 + 3 * omega := by
  constructor
  · intro h
    have h3 : lambda ∣ 3 * omega := (dvd_pow_self lambda two_ne_zero).trans
      (by rw [lambda_sq]; exact ⟨-1, by ring⟩)
    have h1 : lambda ∣ (1 : O) := by
      have e : (1 : O) = (1 + 3 * omega) - 3 * omega := by ring
      rw [e]
      exact dvd_sub h h3
    exact lambda_prime.not_unit (isUnit_of_dvd_one h1)
  · intro h
    apply not_two_dvd_one_add_omega
    have e : 1 + omega = 1 + 3 * omega - 2 * omega := by ring
    rw [e]
    exact dvd_sub h (dvd_mul_right _ _)

/-- `1 + 2λ ≡ 1 (mod 2λ)` but `χ(1 + 2λ) ≠ 1`. -/
theorem twoCubicOf_one_add_two_lambda_ne_one : twoCubicOf (1 + 2 * lambda) ≠ 1 := by
  have h3 : omega ^ 3 = 1 := omega_primitive.pow_eq_one
  have he : (1 + 2 * lambda) * omega = -2 - 3 * omega := by
    rw [lambda]; linear_combination (2 : O) * omega_sq
  have hp : lambda ^ 2 ∣ (-2 - 3 * omega) - 1 := by
    rw [lambda_sq]
    exact ⟨omega ^ 2 * (1 + omega), by linear_combination (3 + 3 * omega) * h3⟩
  rw [twoCubicOf, ← Ideal.span_singleton_mul_right_unit omega_isUnit, he,
    twoCubicValue_span_primary hp, Ne, twoChar_mk_eq_one_iff]
  intro h
  apply not_two_dvd_one_add_omega
  have e : 1 + omega = -(-2 - 3 * omega - 1) - 2 * (1 + omega) := by ring
  rw [e]
  exact dvd_sub (dvd_neg.mpr h) (dvd_mul_right _ _)

theorem good_one_add_two_lambda :
    ¬ lambda ∣ 1 + 2 * lambda ∧ ¬ (2 : O) ∣ 1 + 2 * lambda := by
  constructor
  · intro h
    have h1 : lambda ∣ (1 : O) := by
      have e : (1 : O) = (1 + 2 * lambda) - 2 * lambda := by ring
      rw [e]
      exact dvd_sub h (dvd_mul_left _ _)
    exact lambda_prime.not_unit (isUnit_of_dvd_one h1)
  · intro h
    have h1 : (2 : O) ∣ 1 := by
      have e : (1 : O) = (1 + 2 * lambda) - 2 * lambda := by ring
      rw [e]
      exact dvd_sub h (dvd_mul_right _ _)
    exact two_prime.not_unit (isUnit_of_dvd_one h1)

local instance : Finite (𝓞 K ⧸ sixModulus.fin) :=
  sixModulus.fin.finiteQuotientOfFreeOfNeBot sixModulus.fin_ne_bot

/-- **The conductor of `χ` is `6`.** A larger conductor contains `3` or `2λ`; but `χ` is
non-trivial on `1 + 3ω ≡ 1 (mod 3)` and on `1 + 2λ ≡ 1 (mod 2λ)`. -/
theorem heckeFiniteConductor_cubicTwoHecke :
    heckeFiniteConductor sixModulus cubicTwoHecke = sixModulus.fin := by
  have hf := (FiniteRing.factorsThrough_iff _ _).mp
    (FiniteRing.factorsThrough_conductorIdeal (finiteHeckeWeight sixModulus cubicTwoHecke))
  have key : ∀ a c : O, ¬ lambda ∣ a → ¬ (2 : O) ∣ a → a - 1 = c →
      c ∈ heckeFiniteConductor sixModulus cubicTwoHecke → twoCubicOf a = 1 := by
    intro a c hl h2 hac hc
    have hu := isUnit_mk_six hl h2
    have h1 := hf hu.unit (by
      rw [IsUnit.unit_spec, ← map_one (Ideal.Quotient.mk _), ← map_sub, hac]
      exact hc)
    rw [IsUnit.unit_spec, finiteHeckeWeight_cubicTwoHecke hu, ← map_one ringComplex] at h1
    exact ringComplex_injective h1
  have h3 : (3 : O) ∉ heckeFiniteConductor sixModulus cubicTwoHecke := fun h =>
    twoCubicOf_one_add_three_omega_ne_one (key _ (3 * omega) good_one_add_three_omega.1
      good_one_add_three_omega.2 (by ring) (Ideal.mul_mem_right _ _ h))
  have h2l : 2 * lambda ∉ heckeFiniteConductor sixModulus cubicTwoHecke := fun h =>
    twoCubicOf_one_add_two_lambda_ne_one (key _ (2 * lambda) good_one_add_two_lambda.1
      good_one_add_two_lambda.2 (by ring) h)
  have hle := modulus_le_heckeFiniteConductor sixModulus cubicTwoHecke
  have hgen := Ideal.span_singleton_generator (heckeFiniteConductor sixModulus cubicTwoHecke)
  rw [← hgen] at h3 h2l hle ⊢
  set d := Submodule.IsPrincipal.generator (heckeFiniteConductor sixModulus cubicTwoHecke)
  have hd6 : d ∣ 6 := Ideal.mem_span_singleton.mp (hle (Ideal.mem_span_singleton_self 6))
  have hd3 : ¬ d ∣ 3 := fun h => h3 (Ideal.mem_span_singleton.mpr h)
  have hd2l : ¬ d ∣ 2 * lambda := fun h => h2l (Ideal.mem_span_singleton.mpr h)
  have hd' : d ∣ 2 * lambda ^ 2 := by
    rw [six_eq] at hd6
    exact (neg_omega_sq_isUnit.dvd_mul_right).mp hd6
  obtain ⟨d₁, d₂, h1, h2, hd⟩ := exists_dvd_and_dvd_of_dvd_mul hd'
  rw [hd] at hd3 hd2l ⊢
  rcases two_prime.irreducible.dvd_iff.mp h1 with hu | ha
  · exact absurd ((hu.mul_left_dvd).mpr (h2.trans lambda_sq_dvd_three)) hd3
  · obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow lambda_prime 2).mp h2
    interval_cases i
    · exact absurd (mul_dvd_mul h1 (hassoc.dvd.trans (by simp))) hd2l
    · exact absurd (mul_dvd_mul h1 (hassoc.dvd.trans (by simp))) hd2l
    · have hass : Associated (2 * lambda ^ 2) (d₁ * d₂) := ha.mul_mul hassoc.symm
      change _ = Ideal.span {(6 : O)}
      rw [six_eq, Ideal.span_singleton_mul_right_unit neg_omega_sq_isUnit]
      exact Ideal.span_singleton_eq_span_singleton.mpr hass.symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CubeRootsOfTwo
