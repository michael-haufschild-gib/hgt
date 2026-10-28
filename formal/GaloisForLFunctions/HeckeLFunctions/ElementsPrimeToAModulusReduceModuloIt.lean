import Mathlib

/-!
# Elements prime to a modulus reduce modulo it

A modulus `𝔪 = 𝔪₀ 𝔪∞` of a number field `K` is a non-zero ideal `𝔪₀` of `𝓞_K` together with a set
`𝔪∞` of real places. An element `α ∈ Kˣ` is prime to `𝔪` if its valuation is `1` at every prime
dividing `𝔪₀` (`primeToUnits`). Such an element is a fraction `a/b` with `a, b ∈ 𝓞_K` units modulo
`𝔪₀` (`exists_unit_fraction`, Chinese remainder theorem), which defines the reduction
`K_𝔪 → (𝓞_K/𝔪₀)ˣ` (`reduce`). With the signs at the real places of `𝔪∞` (`signAt`) it gives the
homomorphism `K_𝔪 → (𝓞_K/𝔪₀)ˣ × {±1}^{𝔪∞}` (`rayHom`) whose kernel is the ray group
`K^{𝔪,1}_+` of elements `≡ 1 mod^× 𝔪₀` and positive at `𝔪∞` (`rayGroup`).
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical

namespace GaloisForLFunctions.HeckeLFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- A **modulus** `𝔪 = 𝔪₀ 𝔪∞`: a non-zero ideal of `𝓞_K` and a set of real places. -/
structure Modulus where
  /-- The finite part `𝔪₀`. -/
  fin : Ideal (𝓞 K)
  fin_ne_bot : fin ≠ ⊥
  /-- The infinite part `𝔪∞`: a set of real places. -/
  inf : Set {w : InfinitePlace K // w.IsReal}

variable {K}

/-- The primes dividing `𝔪₀` are finitely many. -/
theorem finite_primes_dvd (𝔪 : Modulus K) :
    {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔪.fin}.Finite :=
  Ideal.finite_factors 𝔪.fin_ne_bot

/-- An element of `𝓞_K` lying in no prime dividing `𝔪₀` is a unit modulo `𝔪₀`. -/
theorem isUnit_mk_of_forall_not_mem (𝔪 : Modulus K) {r : 𝓞 K}
    (hr : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → r ∉ v.asIdeal) :
    IsUnit (Ideal.Quotient.mk 𝔪.fin r) := by
  have hsup : Ideal.span {r} ⊔ 𝔪.fin = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    have hM0 : M ≠ ⊥ := fun h0 => 𝔪.fin_ne_bot (le_bot_iff.mp (h0 ▸ le_sup_right.trans hle))
    let v : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hM0⟩
    exact hr v (Ideal.dvd_iff_le.mpr (le_sup_right.trans hle))
      (hle (le_sup_left (a := Ideal.span {r}) (Ideal.mem_span_singleton_self r)))
  obtain ⟨x, hx, m, hm, hxm⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := (1 : 𝓞 K)))
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk 𝔪.fin s, ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔪.fin), Ideal.Quotient.eq]
  have : r * s - 1 = -m := by linear_combination hxm
  rw [this]
  exact 𝔪.fin.neg_mem hm

/-- A unit modulo `𝔪₀` lies in no prime dividing `𝔪₀`. -/
theorem not_mem_of_isUnit_mk (𝔪 : Modulus K) {r : 𝓞 K} (hr : IsUnit (Ideal.Quotient.mk 𝔪.fin r))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔪.fin) : r ∉ v.asIdeal := by
  intro hrv
  obtain ⟨s, hs⟩ := hr.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔪.fin), Ideal.Quotient.eq] at hs
  have h1 : r * s - 1 ∈ v.asIdeal := Ideal.dvd_iff_le.mp hv hs
  have h2 : r * s ∈ v.asIdeal := v.asIdeal.mul_mem_right s hrv
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using sub_mem h2 h1))

variable (𝔪 : Modulus K)

/-- The group `K_𝔪` of elements prime to `𝔪`: valuation `1` at every prime dividing `𝔪₀`. -/
def primeToUnits : Subgroup Kˣ where
  carrier := {α | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → valuation K v (α : K) = 1}
  mul_mem' {α β} hα hβ v hv := by
    rw [Units.val_mul, map_mul, hα v hv, hβ v hv, one_mul]
  one_mem' v _ := by rw [Units.val_one, map_one]
  inv_mem' {α} hα v hv := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hα v hv, inv_one]

/-- **Unit fractions**: an element prime to `𝔪` is `a/b` with `a, b ∈ 𝓞_K` lying in no prime
dividing `𝔪₀`. The denominator `b` comes from the Chinese remainder theorem: `b ≡ 1` at the primes
of `𝔪₀` and `b` divisible by the denominator of `α` elsewhere. -/
theorem exists_unit_fraction {α : Kˣ} (hα : α ∈ primeToUnits 𝔪) :
    ∃ a b : 𝓞 K, b ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin →
      a ∉ v.asIdeal ∧ b ∉ v.asIdeal) ∧ algebraMap (𝓞 K) K b * α = algebraMap (𝓞 K) K a := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (α : K)
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : algebraMap (𝓞 K) K y ≠ 0 := by simpa using hy0
  set T := {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔪.fin} with hTdef
  have hT : T.Finite := finite_primes_dvd 𝔪
  set D := {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ Ideal.span {y}} with hDdef
  have hD : D.Finite := Ideal.finite_factors (by simpa using hy0)
  -- the exponent of `w` in `y`
  set c : HeightOneSpectrum (𝓞 K) → ℕ := fun w =>
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {y})).factors with hc
  set s := (hT.union hD).toFinset with hs
  obtain ⟨b, hb⟩ := exists_forall_sub_mem_ideal (s := s) (fun w : HeightOneSpectrum (𝓞 K) =>
    w.asIdeal) (fun w => if w ∈ T then 1 else c w) (fun w _ => w.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if (w : HeightOneSpectrum (𝓞 K)) ∈ T then 1 else 0)
  -- `b ≡ 1` at the primes of `𝔪₀`
  have hbT : ∀ v ∈ T, b ∉ v.asIdeal := by
    intro v hv hbv
    have h := hb v (by rw [hs, Set.Finite.mem_toFinset]; exact Or.inl hv)
    simp only [if_pos hv, pow_one] at h
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using sub_mem hbv h))
  -- `b` is divisible by the denominator `y` at the other primes of `y`
  have hbD : ∀ w ∈ D, w ∉ T → w.intValuation b ≤ w.intValuation y := by
    intro w hwD hwT
    have h := hb w (by rw [hs, Set.Finite.mem_toFinset]; exact Or.inr hwD)
    simp only [if_neg hwT, sub_zero] at h
    rw [intValuation_def (r := y), if_neg hy0]
    exact (intValuation_le_pow_iff_mem w b (c w)).mpr h
  -- the case `𝔪₀ = (1)`: no prime divides `𝔪₀`
  by_cases hTe : T = ∅
  · refine ⟨x, y, hy0, fun v hv => absurd (show v ∈ T from hv) (by rw [hTe]; exact id), ?_⟩
    rw [← hxy]
    field_simp
  have hb0 : b ≠ 0 := by
    obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hTe
    exact fun h => hbT v hv (h ▸ v.asIdeal.zero_mem)
  -- `b α` is integral at every prime
  have hint : ∀ w : HeightOneSpectrum (𝓞 K),
      valuation K w (algebraMap (𝓞 K) K b * α) ≤ 1 := by
    intro w
    rw [map_mul, ← hxy, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
      valuation_of_algebraMap]
    have hyw : w.intValuation y ≠ 0 := intValuation_ne_zero w y hy0
    by_cases hwT : w ∈ T
    · have h1 : w.intValuation b = 1 := by
        rcases (intValuation_le_one w b).lt_or_eq with h | h
        · exact absurd ((intValuation_lt_one_iff_mem w b).mp h) (hbT w hwT)
        · exact h
      have h2 := hα w hwT
      rw [← hxy, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap] at h2
      rw [h1, one_mul, h2]
    · by_cases hwD : w ∈ D
      · calc w.intValuation b * (w.intValuation x / w.intValuation y)
            ≤ w.intValuation y * (w.intValuation x / w.intValuation y) :=
              mul_le_mul_left (hbD w hwD hwT) _
          _ = w.intValuation x := by rw [mul_div_cancel₀ _ hyw]
          _ ≤ 1 := intValuation_le_one w x
      · have hyw1 : w.intValuation y = 1 := by
          rcases (intValuation_le_one w y).lt_or_eq with h | h
          · exact absurd (Ideal.dvd_span_singleton.mpr
              ((intValuation_lt_one_iff_mem w y).mp h)) hwD
          · exact h
        rw [hyw1, div_one]
        exact mul_le_one' (intValuation_le_one w b) (intValuation_le_one w x)
  obtain ⟨a, ha⟩ := mem_integers_of_valuation_le_one K _ hint
  refine ⟨a, b, hb0, fun v hv => ⟨fun hav => ?_, hbT v hv⟩, ha.symm⟩
  -- `a = bα` has valuation `1` at the primes of `𝔪₀`
  have h : valuation K v (algebraMap (𝓞 K) K a) < 1 := (valuation_lt_one_iff_mem (K := K) v a).mpr hav
  rw [ha, map_mul, hα v hv, mul_one, valuation_of_algebraMap] at h
  exact hbT v hv ((intValuation_lt_one_iff_mem v b).mp h)

/-- A choice of unit fraction `α = a/b` for `α ∈ K_𝔪`. -/
def unitFraction (α : primeToUnits 𝔪) : 𝓞 K × 𝓞 K :=
  ((exists_unit_fraction 𝔪 α.2).choose, (exists_unit_fraction 𝔪 α.2).choose_spec.choose)

theorem unitFraction_spec (α : primeToUnits 𝔪) :
    (unitFraction 𝔪 α).2 ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin →
      (unitFraction 𝔪 α).1 ∉ v.asIdeal ∧ (unitFraction 𝔪 α).2 ∉ v.asIdeal) ∧
      algebraMap (𝓞 K) K (unitFraction 𝔪 α).2 * (α : Kˣ) =
        algebraMap (𝓞 K) K (unitFraction 𝔪 α).1 :=
  (exists_unit_fraction 𝔪 α.2).choose_spec.choose_spec

/-- The unit `r mod 𝔪₀` of an element lying in no prime of `𝔪₀`. -/
def unitMod {r : 𝓞 K} (hr : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → r ∉ v.asIdeal) :
    (𝓞 K ⧸ 𝔪.fin)ˣ :=
  (isUnit_mk_of_forall_not_mem 𝔪 hr).unit

theorem coe_unitMod {r : 𝓞 K}
    (hr : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → r ∉ v.asIdeal) :
    (unitMod 𝔪 hr : 𝓞 K ⧸ 𝔪.fin) = Ideal.Quotient.mk 𝔪.fin r := rfl

theorem unitMod_mul {a b : 𝓞 K}
    (ha : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → a ∉ v.asIdeal)
    (hb : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → b ∉ v.asIdeal)
    (hab : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → a * b ∉ v.asIdeal) :
    unitMod 𝔪 hab = unitMod 𝔪 ha * unitMod 𝔪 hb := by
  ext
  simp [coe_unitMod, map_mul]

/-- The reduction `α = a/b ↦ a b⁻¹ mod 𝔪₀`. -/
def reduceFun (α : primeToUnits 𝔪) : (𝓞 K ⧸ 𝔪.fin)ˣ :=
  unitMod 𝔪 (fun v hv => ((unitFraction_spec 𝔪 α).2.1 v hv).1) *
    (unitMod 𝔪 (fun v hv => ((unitFraction_spec 𝔪 α).2.1 v hv).2))⁻¹

/-- The reduction does not depend on the unit fraction. -/
theorem reduceFun_eq (α : primeToUnits 𝔪) {a b : 𝓞 K}
    (ha : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → a ∉ v.asIdeal)
    (hb : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → b ∉ v.asIdeal)
    (h : algebraMap (𝓞 K) K b * (α : Kˣ) = algebraMap (𝓞 K) K a) :
    reduceFun 𝔪 α = unitMod 𝔪 ha * (unitMod 𝔪 hb)⁻¹ := by
  obtain ⟨-, -, h'⟩ := unitFraction_spec 𝔪 α
  rw [reduceFun, mul_inv_eq_iff_eq_mul, mul_assoc, mul_comm _ (unitMod 𝔪 _), ← mul_assoc,
    eq_mul_inv_iff_mul_eq]
  ext
  simp only [Units.val_mul, coe_unitMod, ← map_mul]
  congr 1
  -- `a' b = a b'` in `𝓞_K`
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [map_mul, map_mul, ← h, ← h']
  ring

/-- The **reduction** `K_𝔪 → (𝓞_K/𝔪₀)ˣ`, `a/b ↦ a b⁻¹`. -/
def reduce : primeToUnits 𝔪 →* (𝓞 K ⧸ 𝔪.fin)ˣ where
  toFun := reduceFun 𝔪
  map_one' := by
    rw [reduceFun_eq 𝔪 1 (a := 1) (b := 1) (fun v _ h => v.isPrime.ne_top
      ((Ideal.eq_top_iff_one _).mpr h)) (fun v _ h => v.isPrime.ne_top
      ((Ideal.eq_top_iff_one _).mpr h)) (by simp)]
    exact mul_inv_cancel _
  map_mul' α β := by
    obtain ⟨-, hα, hα'⟩ := unitFraction_spec 𝔪 α
    obtain ⟨-, hβ, hβ'⟩ := unitFraction_spec 𝔪 β
    have hnum : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin →
        (unitFraction 𝔪 α).1 * (unitFraction 𝔪 β).1 ∉ v.asIdeal := fun v hv h =>
      (v.isPrime.mem_or_mem h).elim (hα v hv).1 (hβ v hv).1
    have hden : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin →
        (unitFraction 𝔪 α).2 * (unitFraction 𝔪 β).2 ∉ v.asIdeal := fun v hv h =>
      (v.isPrime.mem_or_mem h).elim (hα v hv).2 (hβ v hv).2
    rw [reduceFun_eq 𝔪 (α * β) hnum hden (by
      rw [Subgroup.coe_mul, Units.val_mul, map_mul, map_mul, ← hα', ← hβ']
      ring)]
    rw [unitMod_mul 𝔪 (fun v hv => (hα v hv).1) (fun v hv => (hβ v hv).1),
      unitMod_mul 𝔪 (fun v hv => (hα v hv).2) (fun v hv => (hβ v hv).2), mul_inv, reduceFun,
      reduceFun]
    exact mul_mul_mul_comm _ _ _ _

theorem reduce_eq (α : primeToUnits 𝔪) {a b : 𝓞 K}
    (ha : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → a ∉ v.asIdeal)
    (hb : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → b ∉ v.asIdeal)
    (h : algebraMap (𝓞 K) K b * (α : Kˣ) = algebraMap (𝓞 K) K a) :
    reduce 𝔪 α = unitMod 𝔪 ha * (unitMod 𝔪 hb)⁻¹ :=
  reduceFun_eq 𝔪 α ha hb h

variable (K) in
/-- The **sign** at the real places: `α ↦ (sgn w(α))_w`. -/
def signAt : Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℤˣ) where
  toFun α w := if 0 < InfinitePlace.embedding_of_isReal w.2 (α : K) then 1 else -1
  map_one' := by
    funext w
    simp
  map_mul' α β := by
    funext w
    have hα : InfinitePlace.embedding_of_isReal w.2 (α : K) ≠ 0 := by simp
    have hβ : InfinitePlace.embedding_of_isReal w.2 (β : K) ≠ 0 := by simp
    simp only [Units.val_mul, map_mul, Pi.mul_apply]
    rcases hα.lt_or_gt with ha | ha <;> rcases hβ.lt_or_gt with hb | hb
    · simp [mul_pos_of_neg_of_neg ha hb, not_lt.mpr ha.le, not_lt.mpr hb.le]
    · simp [not_lt.mpr (mul_neg_of_neg_of_pos ha hb).le, not_lt.mpr ha.le, hb]
    · simp [not_lt.mpr (mul_neg_of_pos_of_neg ha hb).le, ha, not_lt.mpr hb.le]
    · simp [mul_pos ha hb, ha, hb]

/-- The signs at the places of `𝔪∞`. -/
def signAtInf : Kˣ →* (𝔪.inf → ℤˣ) :=
  (MonoidHom.pi fun w : 𝔪.inf => Pi.evalMonoidHom (fun _ : {w : InfinitePlace K // w.IsReal} => ℤˣ)
    w.1).comp (signAt K)

omit [NumberField K] in
theorem signAtInf_apply (α : Kˣ) (w : 𝔪.inf) :
    signAtInf 𝔪 α w = if 0 < InfinitePlace.embedding_of_isReal w.1.2 (α : K) then 1 else -1 := rfl

/-- The homomorphism `K_𝔪 → (𝓞_K/𝔪₀)ˣ × {±1}^{𝔪∞}`. -/
def rayHom : primeToUnits 𝔪 →* (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) :=
  (reduce 𝔪).prod ((signAtInf 𝔪).comp (primeToUnits 𝔪).subtype)

/-- The **ray group** `K^{𝔪,1}_+`: elements `≡ 1 mod^× 𝔪₀` and positive at the places of `𝔪∞`. -/
def rayGroup : Subgroup Kˣ := (rayHom 𝔪).ker.map (primeToUnits 𝔪).subtype

theorem rayGroup_le : rayGroup 𝔪 ≤ primeToUnits 𝔪 := by
  rintro _ ⟨α, -, rfl⟩
  exact α.2

/-- `K_𝔪 / K^{𝔪,1}_+` embeds in the finite group `(𝓞_K/𝔪₀)ˣ × {±1}^{𝔪∞}`. -/
instance : Finite ((𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)) := by
  have : Finite (𝓞 K ⧸ 𝔪.fin) := Ring.HasFiniteQuotients.finiteQuotient 𝔪.fin_ne_bot
  infer_instance

end GaloisForLFunctions.HeckeLFunctions
