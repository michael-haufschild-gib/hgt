import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedTypesCompatibility

/-! Reduction of a lifted root of unity depends only on its prime-to-residue-characteristic
part. The normalized type data therefore give the residue compatibility of the host. -/

noncomputable section
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.CyclotomicNorms
open WindowedLandauTheory.MainNotions.N
open scoped Classical

namespace WindowedLandauTheory.NormalizedTypes

section Reduction

variable {Ω : Type} [Field Ω]

private theorem mem_of_pow_eq_one (B : ValuationSubring Ω) {z : Ω} {n : ℕ}
    (hn : 0 < n) (hz : z ^ n = 1) : z ∈ B := by
  rcases B.mem_or_inv_mem z with h | h
  · exact h
  · have he : z = z⁻¹ ^ (n - 1) := by
      have h₁ : z ^ (n - 1) * z = 1 := by rw [← pow_succ, Nat.sub_add_cancel hn, hz]
      rw [inv_pow]
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h₁)
    rw [he]
    exact pow_mem h _

variable (B : ValuationSubring Ω) {l : ℕ} [Fact l.Prime]
variable (κ : IsLocalRing.ResidueField B ≃+* Fbar l)

theorem redThrough_pow {z : Ω} (hz : z ∈ B) (n : ℕ) :
    redThrough B κ (z ^ n) = redThrough B κ z ^ n := by
  simp only [redThrough, dif_pos (pow_mem hz n), dif_pos hz]
  exact map_pow (κ.toRingHom.comp (IsLocalRing.residue B)) (⟨z, hz⟩ : B) n

private theorem pow_eq_one_of_charP (x : Fbar l) (a m : ℕ) (h : x ^ (l ^ a * m) = 1) :
    x ^ m = 1 := by
  have h₁ : (x ^ m - 1) ^ (l ^ a) = 0 := by
    rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm m, h, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).mp h₁)

/-- The `l`-primary component of a finite order element disappears upon reduction. -/
theorem redThrough_primeToPart {M : Type} [Monoid M]
    (t : M →* Ω) (u : M) (hu : 0 < orderOf u) :
    redThrough B κ (t (primeToPart l u)) = redThrough B κ (t u) := by
  have hB : t u ∈ B := mem_of_pow_eq_one B hu (by rw [← map_pow, pow_orderOf_eq_one, map_one])
  let y := redThrough B κ (t u)
  let m := orderOf u
  let a := m.factorization l
  let m' := m / l ^ a
  have hm : l ^ a * m' = m := Nat.ordProj_mul_ordCompl_eq_self m l
  have hy : y ^ m = 1 := by
    change redThrough B κ (t u) ^ orderOf u = 1
    rw [← redThrough_pow B κ hB, ← map_pow, pow_orderOf_eq_one, map_one, redThrough,
      dif_pos (one_mem B)]
    exact map_one κ
  have hy' : y ^ m' = 1 := pow_eq_one_of_charP y a m' (by rw [hm]; exact hy)
  have hm₀ : m' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm
    exact hu.ne' hm.symm
  haveI : NeZero m' := ⟨hm₀⟩
  have hcop : Nat.Coprime (l ^ a) m' :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl (Fact.out : l.Prime) hu.ne')
  have hc : ((l ^ a * ((l ^ a : ℕ) : ZMod m')⁻¹.val : ℕ) : ZMod m') = ((1 : ℕ) : ZMod m') := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hcop
  rw [ZMod.natCast_eq_natCast_iff'] at hc
  unfold primeToPart
  rw [map_pow, redThrough_pow B κ hB]
  change y ^ (l ^ a * ((l ^ a : ℕ) : ZMod m')⁻¹.val) = y
  rw [pow_eq_pow_mod _ hy', hc, ← pow_eq_pow_mod _ hy', pow_one]

theorem IsTeich.injective {A : ValuationSubring Ω}
    {κ : IsLocalRing.ResidueField A ≃+* Fbar l} {t : Fbar l →* Ω} (h : IsTeich A κ t) :
    Function.Injective t := by
  intro x y hxy
  obtain ⟨hx, ex⟩ := h x
  obtain ⟨hy, ey⟩ := h y
  rw [← ex, ← ey]
  exact congrArg (κ ∘ IsLocalRing.residue A) (Subtype.ext hxy)

theorem IsTeich.map_zero {A : ValuationSubring Ω}
    {κ : IsLocalRing.ResidueField A ≃+* Fbar l} {t : Fbar l →* Ω} (h : IsTeich A κ t) :
    t 0 = 0 := by
  have h₀ : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
  by_contra hne
  have h₁ : t 0 = 1 := mul_left_cancel₀ hne (by rw [h₀, mul_one])
  obtain ⟨hx, ex⟩ := h 0
  have he : (⟨t 0, hx⟩ : A) = 1 := Subtype.ext h₁
  rw [he, map_one, map_one] at ex
  exact one_ne_zero ex

end Reduction

/-- Residue comparison at the auxiliary places after taking the prime-to-residue part. -/
def GlobalDatumRegularity (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (u : (ZMod (D.host.g k))ˣ) (y : D.nd.O i),
    D.nd.l i ≠ D.host.g k →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    let z := algebraMap (ZMod (D.host.g k)) (Fbar (D.host.g k)) (u : ZMod (D.host.g k))
    D.naut.iotaQC i (D.naut.iotaQ i (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) y)) =
      D.ntypes.teichC k z →
    D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y) =
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (D.ntypes.iota k v (D.nd.w i) (primeToPart (D.what₂.places.resChar (D.nd.w i)) z))

variable {D : D7} {jE : D.host.E →+* AlgebraicClosure ℚ}

theorem iota_indep (T : NormalizedTypesCompatibility D jE)
    (i : D.nd.Loc) (k : Fin 2) (v v' : D.nd.PlG k) :
    D.ntypes.iota k v (D.nd.w i) = D.ntypes.iota k v' (D.nd.w i) := by
  obtain ⟨B, κ, -, h⟩ := T.iota_loc i
  ext x
  rw [h, h]

theorem globalDatumRegularity_of_typesCompatibility (T : NormalizedTypesCompatibility D jE) :
    GlobalDatumRegularity D := by
  intro i k v u y _ z hy
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  letI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨B, κ, hcomp, hiota⟩ := T.iota_loc i
  obtain ⟨hyB, hyκ⟩ := hcomp y
  rw [← hyκ]
  congr 1
  have hz : z ^ orderOf u = 1 := by
    rw [show z = algebraMap (ZMod (D.host.g k)) (Fbar (D.host.g k)) u.val from rfl,
      ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  have hpos : 0 < orderOf z :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, orderOf_pos u, hz⟩).orderOf_pos
  rw [hiota, redThrough_primeToPart B κ (D.ntypes.teichC k) z hpos, redThrough]
  have hzB : D.ntypes.teichC k z ∈ B := hy ▸ hyB
  rw [dif_pos hzB]
  congr 2
  exact Subtype.ext hy

end WindowedLandauTheory.NormalizedTypes
