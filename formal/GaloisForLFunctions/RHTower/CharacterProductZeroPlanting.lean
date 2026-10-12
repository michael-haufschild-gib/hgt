import GaloisForLFunctions.HTGeometry.PrimeProgressionReciprocalDivergence
import GaloisForLFunctions.HTGeometry.PeriodicCharacterDecomposition
import GaloisForLFunctions.RHTower.PerturbationZero

/-!
# Planting a zero in a combination of character Euler products

**Theorem** (`exists_charProduct_zero`).  Let `C` be a function on the Dirichlet characters
mod `N` with `C(χ₁) ≠ 0` and `C(χ₂) ≠ 0` for two characters `χ₁ ≠ χ₂`.  Then there are `σ > 1`, a
finite set `S` of primes coprime to `N`, and values `z_p` with `|z_p| ≤ p^{−σ}`, such that

`Σ_χ C(χ) Π_{p ∈ S} (1 − χ(p) z_p)^{−1} = 0`.

This is the Bohr-lift form of the Davenport–Heilbronn mechanism: two characters cannot share a
zero-free Euler product.

**Proof.**
1. *Model.*  With `⟨χ, u⟩ = Σ_a χ(a) u(a)` and the dual vectors `v_ψ = φ(N)^{−1} ψ⁻¹`
   (`⟨χ, v_ψ⟩ = δ_{χψ}`), choose `u⁰` with `⟨χ₁, u⁰⟩ = 0`, `⟨χ₂, u⁰⟩ = log(−C(χ₁)/C(χ₂))` and
   `⟨χ, u⁰⟩ = −R'` otherwise.  Then `M(λ) = Σ_χ C(χ) exp⟨χ, u⁰ + λ v_{χ₂}⟩` is
   `C(χ₁)(1 − e^λ) + O(e^{−R'})`.
2. *Realization.*  Dirichlet divergence gives finite sets `S_a` of primes `≡ a` with
   `Σ_{S_a} p^{−σ} > R` for some `σ > 1`.  Spread `u(a)` over `S_a`:
   `z_p = u(p mod N) p^{−σ}/R(p mod N)`.  Then `Σ_p χ(p) z_p = ⟨χ, u⟩` exactly, and
   `log Π_p (1 − χ(p) z_p)^{−1} = ⟨χ, u⟩ + O(K²/R)`.
3. *Zero.*  For `R` large the perturbation is `≤ |C(χ₁)|/12` on `|λ| ≤ 1`, while
   `|C(χ₁)(1 − e^λ)| ≥ |C(χ₁)|/4` on `|λ| = ½`.  Sphere domination (`exists_zero_of_sphere_domination`)
   plants a zero.
-/

open Complex Filter Topology Metric

namespace RHTower

namespace CharacterZeroPlanting

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ} [NeZero N]

/-! ### Pairing and dual vectors -/

/-- The pairing `⟨χ, u⟩ = Σ_a χ(a) u(a)`. -/
def charPair (χ : DirichletCharacter ℂ N) (u : ZMod N → ℂ) : ℂ := ∑ a, χ a * u a

/-- The dual vector `v_ψ = φ(N)^{−1} ψ⁻¹`. -/
def charDual (ψ : DirichletCharacter ℂ N) (a : ZMod N) : ℂ := ((N.totient : ℂ))⁻¹ * ψ⁻¹ a

theorem charPair_add (χ : DirichletCharacter ℂ N) (u v : ZMod N → ℂ) :
    charPair χ (u + v) = charPair χ u + charPair χ v := by
  simp only [charPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem charPair_smul (χ : DirichletCharacter ℂ N) (c : ℂ) (u : ZMod N → ℂ) :
    charPair χ (c • u) = c * charPair χ u := by
  simp only [charPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem charPair_sum (χ : DirichletCharacter ℂ N) {ι : Type*} (s : Finset ι)
    (u : ι → ZMod N → ℂ) : charPair χ (∑ i ∈ s, u i) = ∑ i ∈ s, charPair χ (u i) := by
  simp only [charPair, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- **Orthogonality.**  `⟨χ, v_ψ⟩ = δ_{χψ}`. -/
theorem charPair_charDual (χ ψ : DirichletCharacter ℂ N) :
    charPair χ (charDual ψ) = if χ = ψ then 1 else 0 := by
  have htot : (N.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr
    (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  have e : charPair χ (charDual ψ) = ((N.totient : ℂ))⁻¹ * ∑ a, (χ * ψ⁻¹) a := by
    simp only [charPair, charDual, MulChar.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e]
  by_cases h : χ = ψ
  · rw [if_pos h, h, mul_inv_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
    field_simp
  · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one, mul_zero]
    intro h1
    exact h (mul_inv_eq_one.mp h1)

theorem norm_charPair_le (χ : DirichletCharacter ℂ N) (u : ZMod N → ℂ) :
    ‖charPair χ u‖ ≤ ∑ a, ‖u a‖ := by
  unfold charPair
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ a)

/-! ### Products of `(1 − w)^{−1}` against exponentials -/

theorem one_sub_inv_eq_exp {w : ℂ} (hw : ‖w‖ < 1) :
    (1 - w)⁻¹ = cexp (-Complex.log (1 - w)) := by
  have h0 : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw
    exact lt_irrefl _ hw
  rw [Complex.exp_neg, Complex.exp_log h0]

theorem norm_neg_log_one_sub_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖-Complex.log (1 - w) - w‖ ≤ ‖w‖ ^ 2 := by
  have hw1 : ‖-w‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_one_add_sub_self_le hw1
  rw [norm_neg, ← sub_eq_add_neg] at h
  have e : -Complex.log (1 - w) - w = -(Complex.log (1 - w) - -w) := by ring
  rw [e, norm_neg]
  refine h.trans ?_
  have hpos : 0 < 1 - ‖w‖ := by linarith
  have : (1 - ‖w‖)⁻¹ / 2 ≤ 1 := by
    rw [div_le_one (by norm_num), inv_le_iff_one_le_mul₀ hpos]; linarith
  calc ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 = ‖w‖ ^ 2 * ((1 - ‖w‖)⁻¹ / 2) := by ring
    _ ≤ ‖w‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = ‖w‖ ^ 2 := mul_one _

/-- `|Π (1 − w_p)^{−1} − exp(Σ w_p)| ≤ 2 |exp(Σ w_p)| Σ |w_p|²` when `|w_p| ≤ ½` and
`Σ |w_p|² ≤ 1`. -/
theorem norm_prod_inv_sub_exp_le {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    (hw : ∀ i ∈ S, ‖w i‖ ≤ 1 / 2) (hsq : ∑ i ∈ S, ‖w i‖ ^ 2 ≤ 1) :
    ‖∏ i ∈ S, (1 - w i)⁻¹ - cexp (∑ i ∈ S, w i)‖ ≤
      ‖cexp (∑ i ∈ S, w i)‖ * (2 * ∑ i ∈ S, ‖w i‖ ^ 2) := by
  set E : ℂ := ∑ i ∈ S, (-Complex.log (1 - w i) - w i) with hE
  have hprod : ∏ i ∈ S, (1 - w i)⁻¹ = cexp (∑ i ∈ S, w i) * cexp E := by
    rw [← Complex.exp_add, hE, ← Finset.sum_add_distrib, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [one_sub_inv_eq_exp (by linarith [hw i hi])]
    congr 1; ring
  have hEn : ‖E‖ ≤ ∑ i ∈ S, ‖w i‖ ^ 2 :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => norm_neg_log_one_sub_sub_le (hw i hi))
  rw [hprod, ← mul_sub_one, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (Complex.norm_exp_sub_one_le (hEn.trans hsq)).trans (by linarith)

/-! ### The zero planting -/

/-- `|e^λ − 1| ≥ |λ| − |λ|²` for `|λ| ≤ 1`. -/
theorem norm_cexp_sub_one_ge_sub_sq {x : ℂ} (hx : ‖x‖ ≤ 1) : ‖x‖ - ‖x‖ ^ 2 ≤ ‖cexp x - 1‖ := by
  have h := Complex.norm_exp_sub_one_sub_id_le hx
  have h2 := norm_add_le (x - (cexp x - 1)) (cexp x - 1)
  rw [sub_add_cancel] at h2
  have e : cexp x - 1 - x = -(x - (cexp x - 1)) := by ring
  rw [e, norm_neg] at h
  linarith

/-- **Two characters cannot share a zero-free Euler product.** -/
theorem exists_charProduct_zero {C : DirichletCharacter ℂ N → ℂ} {χ₁ χ₂ : DirichletCharacter ℂ N}
    (h12 : χ₁ ≠ χ₂) (h1 : C χ₁ ≠ 0) (h2 : C χ₂ ≠ 0) :
    ∃ σ : ℝ, 1 < σ ∧ ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ IsUnit (p : ZMod N)) ∧
      ∃ z : ℕ → ℂ, (∀ p ∈ S, ‖z p‖ ≤ (p : ℝ) ^ (-σ)) ∧
        ∑ χ, C χ * ∏ p ∈ S, (1 - χ p * z p)⁻¹ = 0 := by
  classical
  set c₁ : ℝ := ‖C χ₁‖ with hc₁
  have hc₁pos : 0 < c₁ := norm_pos_iff.mpr h1
  set A : ℝ := ∑ χ, ‖C χ‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  /- Step 1: the model. -/
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, Real.exp (-R') * A ≤ c₁ / 24 := by
    have ht : Tendsto (fun R : ℝ => Real.exp (-R) * A) atTop (𝓝 (0 * A)) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.mul_const A
    rw [zero_mul] at ht
    exact (ht.eventually (ge_mem_nhds (by positivity))).exists
  set L₀ : ℂ := Complex.log (-C χ₁ / C χ₂) with hL₀
  have hL₀e : cexp L₀ = -C χ₁ / C χ₂ :=
    Complex.exp_log (div_ne_zero (neg_ne_zero.mpr h1) h2)
  set others : Finset (DirichletCharacter ℂ N) := (Finset.univ.erase χ₁).erase χ₂ with hothers
  set u₀ : ZMod N → ℂ := L₀ • charDual χ₂ - ((R' : ℝ) : ℂ) • ∑ χ ∈ others, charDual χ with hu₀
  set w : ZMod N → ℂ := charDual χ₂ with hw
  have hpair : ∀ (χ : DirichletCharacter ℂ N) (t : ℂ), charPair χ (u₀ + t • w) =
      (if χ = χ₂ then L₀ + t else 0) - (if χ ∈ others then ((R' : ℝ) : ℂ) else 0) := by
    intro χ t
    rw [hu₀, hw, sub_eq_add_neg, charPair_add, charPair_add, charPair_smul, ← neg_smul,
      charPair_smul, charPair_smul, charPair_sum, charPair_charDual]
    have hs : ∑ ψ ∈ others, charPair χ (charDual ψ) = if χ ∈ others then 1 else 0 := by
      simp only [charPair_charDual]
      rw [Finset.sum_ite_eq]
    rw [hs]
    split_ifs <;> ring
  set M : ℂ → ℂ := fun t => ∑ χ, C χ * cexp (charPair χ (u₀ + t • w)) with hM
  have hχ₁o : χ₁ ∉ others := by simp [hothers]
  have hχ₂o : χ₂ ∉ others := by simp [hothers]
  have hMeq : ∀ t : ℂ, M t = C χ₁ * (1 - cexp t) +
      ∑ χ ∈ others, C χ * cexp (-((R' : ℝ) : ℂ)) := by
    intro t
    simp only [hM]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ χ₁),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h12.symm, Finset.mem_univ χ₂⟩)]
    rw [hpair, hpair, if_neg h12, if_neg hχ₁o, if_pos rfl, if_neg hχ₂o]
    have hrest : ∑ χ ∈ others, C χ * cexp (charPair χ (u₀ + t • w)) =
        ∑ χ ∈ others, C χ * cexp (-((R' : ℝ) : ℂ)) := by
      refine Finset.sum_congr rfl fun χ hχ => ?_
      have hne : χ ≠ χ₂ := fun h => hχ₂o (h ▸ hχ)
      rw [hpair, if_neg hne, if_pos hχ, zero_sub]
    rw [hrest]
    simp only [sub_self, sub_zero, Complex.exp_zero, Complex.exp_add, hL₀e]
    have e2 : C χ₂ * (-C χ₁ / C χ₂ * cexp t) = -(C χ₁ * cexp t) := by field_simp
    rw [e2]; ring
  have hMclose : ∀ t : ℂ, ‖M t - C χ₁ * (1 - cexp t)‖ ≤ c₁ / 24 := by
    intro t
    rw [hMeq, add_sub_cancel_left]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ χ ∈ others, ‖C χ * cexp (-((R' : ℝ) : ℂ))‖ = ∑ χ ∈ others, ‖C χ‖ * Real.exp (-R') := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [norm_mul, Complex.norm_exp]; simp
      _ ≤ ∑ χ, ‖C χ‖ * Real.exp (-R') :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => by positivity
      _ = Real.exp (-R') * A := by rw [hA, ← Finset.sum_mul, mul_comm]
      _ ≤ c₁ / 24 := hR'
  /- Step 2: the realization constants. -/
  set K : ℝ := ∑ a, (‖u₀ a‖ + ‖w a‖) + 1 with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ a, (‖u₀ a‖ + ‖w a‖) := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have hu_bound : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ a, ‖(u₀ + t • w) a‖ ≤ K := by
    intro t ht0 a
    have h1' : ‖(u₀ + t • w) a‖ ≤ ‖u₀ a‖ + ‖w a‖ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) ht0
    have h2' : ‖u₀ a‖ + ‖w a‖ ≤ ∑ b, (‖u₀ b‖ + ‖w b‖) :=
      Finset.single_le_sum (f := fun b => ‖u₀ b‖ + ‖w b‖) (fun _ _ => by positivity)
        (Finset.mem_univ a)
    linarith
  have hsumu : ∀ t : ℂ, ‖t‖ ≤ 1 → ∑ a, ‖(u₀ + t • w) a‖ ≤ (Fintype.card (ZMod N)) * K := by
    intro t ht0
    calc ∑ a, ‖(u₀ + t • w) a‖ ≤ ∑ _a : ZMod N, K := Finset.sum_le_sum fun a _ => hu_bound t ht0 a
      _ = (Fintype.card (ZMod N)) * K := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
  set Kt : ℝ := (Fintype.card (ZMod N)) * K with hKt
  have hKt0 : 0 ≤ Kt := by positivity
  -- the size of the realization
  set R : ℝ := 2 * K + K * Kt + (A + 1) * Real.exp Kt * 2 * (K * Kt) * 24 / c₁ + 1 with hRdef
  have hRK : 2 * K ≤ R := by
    have : 0 ≤ (A + 1) * Real.exp Kt * 2 * (K * Kt) * 24 / c₁ := by positivity
    have : 0 ≤ K * Kt := by positivity
    linarith
  have hRKt : K * Kt ≤ R := by
    have : 0 ≤ (A + 1) * Real.exp Kt * 2 * (K * Kt) * 24 / c₁ := by positivity
    linarith
  have hRpos : 0 < R := by linarith
  have hRerr : A * Real.exp Kt * (2 * (K * Kt / R)) ≤ c₁ / 24 := by
    have hB : (A + 1) * Real.exp Kt * 2 * (K * Kt) * 24 / c₁ ≤ R := by
      have : 0 ≤ 2 * K := by positivity
      have : 0 ≤ K * Kt := by positivity
      linarith
    have hAle : A * Real.exp Kt * (2 * (K * Kt)) ≤ (A + 1) * Real.exp Kt * (2 * (K * Kt)) := by
      gcongr; linarith
    rw [div_le_iff₀ hc₁pos] at hB
    rw [show A * Real.exp Kt * (2 * (K * Kt / R)) = A * Real.exp Kt * (2 * (K * Kt)) / R by
      field_simp, div_le_iff₀ hRpos]
    nlinarith
  /- Step 3: the primes. -/
  have hS₀ : ∀ a : ZMod N, ∃ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ (p : ZMod N) = a) ∧
      (IsUnit a → R + 1 < ∑ p ∈ T, ((p : ℝ))⁻¹) := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨T, hT, hsum⟩ := exists_finset_primeRecip_gt ha (R + 1)
      exact ⟨T, hT, fun _ => hsum⟩
    · exact ⟨∅, by simp, fun h => absurd h ha⟩
  choose T hTp hTsum using hS₀
  set S : Finset ℕ := Finset.univ.filter (fun a : ZMod N => IsUnit a) |>.biUnion T with hS
  have hSmem : ∀ p ∈ S, p.Prime ∧ IsUnit (p : ZMod N) := by
    intro p hp
    obtain ⟨a, ha, hpa⟩ := Finset.mem_biUnion.mp hp
    have h' := hTp a p hpa
    exact ⟨h'.1, h'.2 ▸ (Finset.mem_filter.mp ha).2⟩
  -- choose `σ > 1`
  have hcont : ∀ a : ZMod N, ∀ᶠ σ in 𝓝 (1 : ℝ),
      IsUnit a → R < ∑ p ∈ T a, ((p : ℝ)) ^ (-σ) := by
    intro a
    by_cases ha : IsUnit a
    · have hc : ContinuousAt (fun σ : ℝ => ∑ p ∈ T a, ((p : ℝ)) ^ (-σ)) 1 := by
        refine (continuous_finsetSum _ fun p hp => ?_).continuousAt
        have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hTp a p hp).1.ne_zero
        exact continuous_const.rpow continuous_neg fun _ => Or.inl hp0
      have hval : ∑ p ∈ T a, ((p : ℝ)) ^ (-(1 : ℝ)) = ∑ p ∈ T a, ((p : ℝ))⁻¹ :=
        Finset.sum_congr rfl fun p _ => Real.rpow_neg_one _
      have := hc.eventually (lt_mem_nhds (show R < ∑ p ∈ T a, ((p : ℝ)) ^ (-(1 : ℝ)) by
        rw [hval]; linarith [hTsum a ha]))
      filter_upwards [this] with σ hσ _ using hσ
    · exact Eventually.of_forall fun _ h => absurd h ha
  obtain ⟨σ, hσall, hσ1⟩ := (((Filter.eventually_all.mpr hcont).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Set.Ioi (1 : ℝ) ∈ 𝓝[>] 1)).exists
  have hσ1' : 1 < σ := hσ1
  /- Step 4: the realization. -/
  set Rf : ZMod N → ℝ := fun a => ∑ p ∈ S.filter (fun p : ℕ => (p : ZMod N) = a), ((p : ℝ)) ^ (-σ) with hRf
  have hRfR : ∀ a : ZMod N, IsUnit a → R < Rf a := by
    intro a ha
    refine (hσall a ha).trans_le (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity)
    intro p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr
      ⟨Finset.mem_univ a, ha⟩, hp⟩, (hTp a p hp).2⟩
  have hRf0 : ∀ a : ZMod N, 0 ≤ Rf a := fun a => Finset.sum_nonneg fun _ _ => by positivity
  have hpσ : ∀ p ∈ S, 0 < ((p : ℝ)) ^ (-σ) ∧ ((p : ℝ)) ^ (-σ) ≤ 1 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hSmem p hp).1.one_lt.le
    exact ⟨Real.rpow_pos_of_pos (by linarith) _,
      Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)⟩
  set zt : ℂ → ℕ → ℂ := fun t p =>
    (u₀ + t • w) (p : ZMod N) * ((((p : ℝ)) ^ (-σ) / Rf (p : ZMod N) : ℝ) : ℂ) with hzt
  have hzt_norm : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ p ∈ S, ‖zt t p‖ ≤ K / R * ((p : ℝ)) ^ (-σ) := by
    intro t ht0 p hp
    have hRp := hRfR _ (hSmem p hp).2
    have hRp0 : 0 < Rf (p : ZMod N) := hRpos.trans hRp
    simp only [hzt, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (div_nonneg (hpσ p hp).1.le hRp0.le)]
    calc ‖(u₀ + t • w) (p : ZMod N)‖ * (((p : ℝ)) ^ (-σ) / Rf (p : ZMod N))
        ≤ K * (((p : ℝ)) ^ (-σ) / R) := by
          refine mul_le_mul (hu_bound t ht0 _) ?_ (by positivity) (by linarith)
          exact div_le_div_of_nonneg_left (hpσ p hp).1.le hRpos hRp.le
      _ = K / R * ((p : ℝ)) ^ (-σ) := by ring
  have hKR : K / R ≤ 1 / 2 := by rw [div_le_iff₀ hRpos]; linarith
  have hz_small : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ p ∈ S, ‖zt t p‖ ≤ ((p : ℝ)) ^ (-σ) / 2 := by
    intro t ht0 p hp
    refine (hzt_norm t ht0 p hp).trans ?_
    have := (hpσ p hp).1
    nlinarith
  have hw_small : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ (χ : DirichletCharacter ℂ N), ∀ p ∈ S,
      ‖χ p * zt t p‖ ≤ 1 / 2 := by
    intro t ht0 χ p hp
    rw [norm_mul]
    have h1' := DirichletCharacter.norm_le_one χ (p : ZMod N)
    have h2' := hz_small t ht0 p hp
    have h3' := (hpσ p hp).2
    calc ‖χ p‖ * ‖zt t p‖ ≤ 1 * (((p : ℝ)) ^ (-σ) / 2) :=
          mul_le_mul h1' h2' (norm_nonneg _) zero_le_one
      _ ≤ 1 / 2 := by linarith
  -- the exact pairing
  have hpair_real : ∀ (t : ℂ) (χ : DirichletCharacter ℂ N),
      ∑ p ∈ S, χ p * zt t p = charPair χ (u₀ + t • w) := by
    intro t χ
    rw [← Finset.sum_fiberwise S (fun p => (p : ZMod N))]
    unfold charPair
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : IsUnit a
    · have hRa : 0 < Rf a := hRpos.trans (hRfR a ha)
      have e : ∀ p ∈ S.filter (fun p : ℕ => (p : ZMod N) = a), χ p * zt t p =
          χ a * (u₀ + t • w) a * ((((p : ℝ)) ^ (-σ) : ℝ) : ℂ) / ((Rf a : ℝ) : ℂ) := by
        intro p hp
        have hpa : (p : ZMod N) = a := (Finset.mem_filter.mp hp).2
        simp only [hzt, hpa]
        push_cast
        ring
      rw [Finset.sum_congr rfl e, ← Finset.sum_div, ← Finset.mul_sum]
      have hsum : ∑ p ∈ S.filter (fun p : ℕ => (p : ZMod N) = a), ((((p : ℝ)) ^ (-σ) : ℝ) : ℂ) = ((Rf a : ℝ) : ℂ) := by
        simp only [hRf]; push_cast; rfl
      rw [hsum]
      have : ((Rf a : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hRa.ne'
      field_simp
    · have hχ : χ a = 0 := MulChar.map_nonunit χ ha
      rw [hχ, zero_mul]
      refine Finset.sum_eq_zero fun p hp => ?_
      have hpa : (p : ZMod N) = a := (Finset.mem_filter.mp hp).2
      exact absurd (hpa ▸ (hSmem p (Finset.mem_filter.mp hp).1).2) ha
  -- the sum of the `|z_p|`
  have hzsum : ∀ t : ℂ, ‖t‖ ≤ 1 → ∑ p ∈ S, ‖zt t p‖ ≤ Kt := by
    intro t ht0
    rw [← Finset.sum_fiberwise S (fun p => (p : ZMod N))]
    refine (Finset.sum_le_sum fun a _ => ?_).trans (hsumu t ht0)
    by_cases hS0 : Rf a = 0
    · have : ∀ p ∈ S.filter (fun p : ℕ => (p : ZMod N) = a), ‖zt t p‖ = 0 := by
        intro p hp
        have hpa : (p : ZMod N) = a := (Finset.mem_filter.mp hp).2
        simp only [hzt, hpa, hS0, div_zero, Complex.ofReal_zero, mul_zero, norm_zero]
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero]; exact norm_nonneg _
    · have hRa : 0 < Rf a := lt_of_le_of_ne (hRf0 a) (Ne.symm hS0)
      have e : ∀ p ∈ S.filter (fun p : ℕ => (p : ZMod N) = a), ‖zt t p‖ =
          ‖(u₀ + t • w) a‖ * (((p : ℝ)) ^ (-σ) / Rf a) := by
        intro p hp
        have hpa : (p : ZMod N) = a := (Finset.mem_filter.mp hp).2
        have hp' := (hpσ p (Finset.mem_filter.mp hp).1).1
        simp only [hzt, hpa, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (div_nonneg hp'.le hRa.le)]
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← Finset.sum_div]
      have : ∑ p ∈ S.filter (fun p : ℕ => (p : ZMod N) = a), ((p : ℝ)) ^ (-σ) = Rf a := rfl
      rw [this, div_self hRa.ne', mul_one]
  have hsq : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ (χ : DirichletCharacter ℂ N),
      ∑ p ∈ S, ‖χ p * zt t p‖ ^ 2 ≤ K * Kt / R := by
    intro t ht0 χ
    have hb : ∀ p ∈ S, ‖χ p * zt t p‖ ^ 2 ≤ K / R * ‖zt t p‖ := by
      intro p hp
      have hn : ‖χ p * zt t p‖ ≤ ‖zt t p‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
      have hzK : ‖zt t p‖ ≤ K / R := (hzt_norm t ht0 p hp).trans
        (mul_le_of_le_one_right (by positivity) (hpσ p hp).2)
      calc ‖χ p * zt t p‖ ^ 2 ≤ ‖zt t p‖ ^ 2 := by gcongr
        _ = ‖zt t p‖ * ‖zt t p‖ := sq _
        _ ≤ K / R * ‖zt t p‖ := mul_le_mul_of_nonneg_right hzK (norm_nonneg _)
    calc ∑ p ∈ S, ‖χ p * zt t p‖ ^ 2 ≤ ∑ p ∈ S, K / R * ‖zt t p‖ := Finset.sum_le_sum hb
      _ = K / R * ∑ p ∈ S, ‖zt t p‖ := by rw [Finset.mul_sum]
      _ ≤ K / R * Kt := mul_le_mul_of_nonneg_left (hzsum t ht0) (by positivity)
      _ = K * Kt / R := by ring
  have hsq1 : K * Kt / R ≤ 1 := by rw [div_le_one hRpos]; exact hRKt
  /- Step 5: the realized function is close to the model. -/
  set Tf : ℂ → ℂ := fun t => ∑ χ, C χ * ∏ p ∈ S, (1 - χ p * zt t p)⁻¹ with hTf
  have hTM : ∀ t : ℂ, ‖t‖ ≤ 1 → ‖Tf t - M t‖ ≤ c₁ / 24 := by
    intro t ht0
    have hterm : ∀ χ : DirichletCharacter ℂ N,
        ‖C χ * ∏ p ∈ S, (1 - χ p * zt t p)⁻¹ - C χ * cexp (charPair χ (u₀ + t • w))‖ ≤
          ‖C χ‖ * (Real.exp Kt * (2 * (K * Kt / R))) := by
      intro χ
      rw [← mul_sub, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h := norm_prod_inv_sub_exp_le S (fun p => χ p * zt t p)
        (fun p hp => hw_small t ht0 χ p hp) ((hsq t ht0 χ).trans hsq1)
      rw [hpair_real] at h
      refine h.trans (mul_le_mul ?_ ?_ (by positivity) (by positivity))
      · exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr
          ((norm_charPair_le χ _).trans (hsumu t ht0)))
      · exact mul_le_mul_of_nonneg_left (hsq t ht0 χ) (by norm_num)
    calc ‖Tf t - M t‖ = ‖∑ χ, (C χ * ∏ p ∈ S, (1 - χ p * zt t p)⁻¹ -
          C χ * cexp (charPair χ (u₀ + t • w)))‖ := by
          simp only [hTf, hM, Finset.sum_sub_distrib]
      _ ≤ ∑ χ, ‖C χ‖ * (Real.exp Kt * (2 * (K * Kt / R))) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => hterm χ)
      _ = A * Real.exp Kt * (2 * (K * Kt / R)) := by rw [← Finset.sum_mul, ← hA]; ring
      _ ≤ c₁ / 24 := hRerr
  /- Step 6: holomorphy. -/
  have hTd : ∀ t : ℂ, ‖t‖ ≤ 1 → DifferentiableAt ℂ Tf t := by
    intro t ht0
    have hz : ∀ p, DifferentiableAt ℂ (fun t' : ℂ => zt t' p) t := by
      intro p
      simp only [hzt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    refine DifferentiableAt.fun_sum fun χ _ => (differentiableAt_const _).mul ?_
    refine DifferentiableAt.fun_finsetProd fun p hp => ?_
    have hne : 1 - χ p * zt t p ≠ 0 := by
      intro h0
      have : χ p * zt t p = 1 := by linear_combination -h0
      have := hw_small t ht0 χ p hp
      rw [‹χ p * zt t p = 1›, norm_one] at this
      norm_num at this
    exact ((differentiableAt_const _).sub ((differentiableAt_const _).mul (hz p))).inv hne
  /- Step 7: the zero. -/
  set hfun : ℂ → ℂ := fun t => C χ₁ * (1 - cexp t) with hhfun
  set gfun : ℂ → ℂ := fun t => Tf t - hfun t with hgfun
  have hball : closure (ball (0 : ℂ) (1 / 2)) ⊆ {t : ℂ | ‖t‖ ≤ 1} := by
    rw [closure_ball _ (by norm_num)]
    intro t ht
    have : ‖t‖ ≤ 1 / 2 := by simpa using ht
    show ‖t‖ ≤ 1
    linarith
  have hhd : DiffContOnCl ℂ hfun (ball 0 (1 / 2)) :=
    (Differentiable.differentiableOn (by simp only [hhfun]; fun_prop)).diffContOnCl
  have hgd : DiffContOnCl ℂ gfun (ball 0 (1 / 2)) := by
    refine DifferentiableOn.diffContOnCl fun t ht => ?_
    have ht' := hball ht
    exact ((hTd t ht').sub (by simp only [hhfun]; fun_prop)).differentiableWithinAt
  obtain ⟨tstar, htstar, hzero⟩ : ∃ t : ℂ, ‖t‖ ≤ 1 ∧ Tf t = 0 := by
    by_cases hg0 : gfun 0 = 0
    · refine ⟨0, by simp, ?_⟩
      have : hfun 0 = 0 := by simp [hhfun]
      have h' : Tf 0 - hfun 0 = 0 := hg0
      rw [this, sub_zero] at h'
      exact h'
    · have hdom : ∀ t ∈ sphere (0 : ℂ) (1 / 2), 3 * ‖gfun t‖ ≤ ‖hfun t‖ := by
        intro t ht
        have htn : ‖t‖ = 1 / 2 := by simpa using ht
        have ht1 : ‖t‖ ≤ 1 := by rw [htn]; norm_num
        have hlow : c₁ / 4 ≤ ‖hfun t‖ := by
          simp only [hhfun, norm_mul]
          rw [← hc₁, norm_sub_rev]
          have := norm_cexp_sub_one_ge_sub_sq ht1
          rw [htn] at this
          nlinarith
        have hup : ‖gfun t‖ ≤ c₁ / 12 := by
          simp only [hgfun]
          calc ‖Tf t - hfun t‖ = ‖(Tf t - M t) + (M t - C χ₁ * (1 - cexp t))‖ := by
                simp only [hhfun]; ring_nf
            _ ≤ ‖Tf t - M t‖ + ‖M t - C χ₁ * (1 - cexp t)‖ := norm_add_le _ _
            _ ≤ c₁ / 24 + c₁ / 24 := add_le_add (hTM t ht1) (hMclose t)
            _ = c₁ / 12 := by ring
        linarith
      obtain ⟨t, ht, htz⟩ := exists_zero_of_sphere_domination (by norm_num) hgd hhd
        (by simp [hhfun]) hg0 hdom
      refine ⟨t, ?_, ?_⟩
      · have : ‖t‖ ≤ 1 / 2 := by simpa using ht
        linarith
      · have : gfun t + hfun t = Tf t := by simp only [hgfun]; ring
        rw [← this]; exact htz
  refine ⟨σ, hσ1', S, hSmem, zt tstar, fun p hp => ?_, hzero⟩
  have := hz_small tstar htstar p hp
  have := (hpσ p hp).1
  linarith

end

end CharacterZeroPlanting

end RHTower
