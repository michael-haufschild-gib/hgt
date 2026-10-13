import GaloisForLFunctions.RHTower.PeriodicExpProducerSingleCharacter

/-!
# Planting a zero across two levels of characters

**Theorem** (`exists_twoLevel_zero_of_far`). Let `χ₁ ≠ χ₂` be characters mod `N` and `C` a
function on the characters mod `N` with `C(χ₁) ≠ 0 ≠ C(χ₂)`. Then there is `η > 0`, depending only
on `N`, `C`, `χ₁`, `χ₂`, with the following property. For every multiple `N'` of `N` and every `P₀`,
let `D` be coefficients on the characters mod `N'` that do not factor through `N`, with
`Σ|D| ≤ |C(χ₁)|/96`. Let `Φ(S, v)` be any far part with `|Φ(S, v)| ≤ η e^{2Σ_S|v_p|}` for `v`
supported on `S` with `|v_p| ≤ ½`, holomorphic along holomorphic families of such `v`. Then there
are `σ > 1`, a finite set `S` of primes `p > P₀` in the unit classes mod `N'`, and values
`|z_p| ≤ p^{−σ}` supported on `S`, with
`Σ_ξ C(ξ) Π_{p∈S}(1 − ξ(p) z_p)^{−1} + Σ_ψ D(ψ) Π_{p∈S}(1 − ψ(p) z_p)^{−1} + Φ(S, z) = 0`.

Two far parts are provided.
* *Products* (`exists_twoLevel_charProduct_zero`): `Φ = Σ_j e_j Π_{p∈S}(1 − g_j(p) z_p)^{−1}` with
  `|g_j| ≤ 1` and `Σ|e_j| ≤ η`.
* *Power series* (`exists_twoLevel_zero_of_powerSeries`): `Φ = Σ_n τ_n f_z(n)` with `|τ_n| ≤ η`,
  where `f_z` is the completely multiplicative function with prime values `z`. The Euler bound
  `Σ_n |f_v(n)| = Π_{p∈S}(1 − |v_p|)^{−1} ≤ e^{2Σ_S|v_p|}` (`summable_norm_primeValueTwist`)
  gives the size condition. This form carries the additive twists `Σ_n e(n x) f(n)` of
  frequencies `x` whose denominators exceed the level, which are not character products.

This is the robust form of the Davenport–Heilbronn mechanism (`exists_charProduct_zero`) needed for
countably many characters of unbounded moduli. The threshold `η` does not depend on `N'`.

**Proof.**
* *Fibres* (`sum_unitsFibre_eq_zero`). A character `ψ` mod `N'` that does not factor through `N` is
  nontrivial on the kernel of `(ℤ/N')ˣ → (ℤ/N)ˣ`, so its sum over every fibre vanishes.
* *Pull-back* (`charPair_pullback_of_not_factorsThrough`, `charPair_changeLevel_pullback`). Spread a
  vector `u` on `ℤ/N` evenly over the fibres. The pairing with an induced character is `⟨ξ, u⟩`,
  the pairing with every other character mod `N'` is `0`, and the `ℓ¹` norm does not grow.
* *Realization at level `N'`* (`exists_realization`). Primes in the unit classes mod `N'` reproduce
  every pairing exactly, with `Σ|z_p|` bounded by the `ℓ¹` norm of the vector.
* *Zero.* Take the model vector of `exists_charProduct_zero` at level `N`
  (`exists_twoLevel_model`). The characters mod `N` then give `C(χ₁)(1 − e^t)` up to `|C(χ₁)|/24`.
  The characters `ψ` see pairing `0`, so each product is within a factor `2` of `1`
  (`prod_inv_estimates`). The far part is at most `η e^{2K}`, where the `ℓ¹` bound `K` depends only
  on the level-`N` model. Sphere domination then plants the zero.
-/

open Complex Filter Topology Metric

namespace RHTower

namespace CharacterZeroPlanting

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Fibres of the units map -/

section Fibres

variable {N N' : ℕ} [NeZero N] [NeZero N'] (hNN : N ∣ N')

/-- The fibre of `(ℤ/N')ˣ → (ℤ/N)ˣ` over `a`. -/
def unitsFibre (a : (ZMod N)ˣ) : Finset (ZMod N')ˣ :=
  Finset.univ.filter fun b => ZMod.unitsMap hNN b = a

/-- The common size of the fibres. -/
def fibreSize : ℕ := (unitsFibre hNN 1).card

omit [NeZero N] in
theorem card_unitsFibre (a : (ZMod N)ˣ) : (unitsFibre hNN a).card = fibreSize hNN := by
  unfold fibreSize unitsFibre
  exact MonoidHom.card_fiber_eq_of_mem_range (ZMod.unitsMap hNN) (ZMod.unitsMap_surjective hNN a)
    (ZMod.unitsMap_surjective hNN 1)

omit [NeZero N] in
theorem fibreSize_pos : 0 < fibreSize hNN := by
  unfold fibreSize
  exact Finset.card_pos.mpr ⟨1, by simp [unitsFibre]⟩

omit [NeZero N] in
/-- **Fibre sums of a character that does not factor through `N` vanish.** -/
theorem sum_unitsFibre_eq_zero {ψ : DirichletCharacter ℂ N'} (hψ : ¬ ψ.FactorsThrough N)
    (a : (ZMod N)ˣ) : ∑ b ∈ unitsFibre hNN a, ψ (b : ZMod N') = 0 := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hNN] at hψ
  obtain ⟨k, hk, hkψ⟩ := SetLike.not_le_iff_exists.mp hψ
  have hk1 : ZMod.unitsMap hNN k = 1 := hk
  have hψk : ψ (k : ZMod N') ≠ 1 := by
    intro h
    apply hkψ
    rw [MonoidHom.mem_ker]
    ext
    rw [MulChar.coe_toUnitHom, h, Units.val_one]
  have hshift : ∑ b ∈ unitsFibre hNN a, ψ ((k * b : (ZMod N')ˣ) : ZMod N') =
      ∑ b ∈ unitsFibre hNN a, ψ (b : ZMod N') := by
    refine Finset.sum_nbij' (fun b => k * b) (fun b => k⁻¹ * b) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      simp only [unitsFibre, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rw [map_mul, hk1, one_mul, hb]
    · intro b hb
      simp only [unitsFibre, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rw [map_mul, map_inv, hk1, inv_one, one_mul, hb]
    · intro b _; simp
    · intro b _; simp
    · intro b _; rfl
  have hmul : ∀ b : (ZMod N')ˣ, ψ ((k * b : (ZMod N')ˣ) : ZMod N') = ψ k * ψ b := by
    intro b; rw [Units.val_mul, map_mul]
  simp_rw [hmul, ← Finset.mul_sum] at hshift
  have h0 : (ψ (k : ZMod N') - 1) * ∑ b ∈ unitsFibre hNN a, ψ (b : ZMod N') = 0 := by
    rw [sub_mul, hshift, one_mul, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hψk
  · exact h

/-- Sums over `ℤ/M` of functions supported on the units are sums over the units. -/
theorem sum_ite_isUnit {M : ℕ} [NeZero M] (f : ZMod M → ℂ) :
    ∑ b, (if IsUnit b then f b else 0) = ∑ b : (ZMod M)ˣ, f b := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun b => (b : ZMod M)) (fun b => if h : IsUnit b then h.unit else 1)
    ?_ ?_ ?_ ?_ ?_
  · intro b _; simp
  · intro b _; simp
  · intro b _; simp
  · intro b hb
    have hb' : IsUnit b := (Finset.mem_filter.mp hb).2
    simp [hb']
  · intro b _; rfl

/-- The pull-back of a vector on `ℤ/N`, spread evenly over the fibres. -/
def pullback (u : ZMod N → ℂ) : ZMod N' → ℂ := fun b =>
  if IsUnit b then u (b.cast : ZMod N) / (fibreSize hNN : ℂ) else 0

omit [NeZero N] in
theorem pullback_add_smul (u w : ZMod N → ℂ) (t : ℂ) :
    pullback hNN (u + t • w) = pullback hNN u + t • pullback hNN w := by
  funext b
  simp only [pullback, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The fibre decomposition of a sum over the units mod `N'`. -/
theorem sum_units_eq_sum_fibres (F : (ZMod N')ˣ → ℂ) :
    ∑ b : (ZMod N')ˣ, F b = ∑ a : (ZMod N)ˣ, ∑ b ∈ unitsFibre hNN a, F b := by
  classical
  exact (Finset.sum_fiberwise Finset.univ (ZMod.unitsMap hNN) F).symm

omit [NeZero N] in
theorem cast_of_mem_unitsFibre {a : (ZMod N)ˣ} {b : (ZMod N')ˣ} (hb : b ∈ unitsFibre hNN a) :
    ((b : ZMod N').cast : ZMod N) = a := by
  have hb' : ZMod.unitsMap hNN b = a := (Finset.mem_filter.mp hb).2
  rw [← ZMod.unitsMap_val hNN b, hb']

theorem charPair_pullback_eq (ψ : DirichletCharacter ℂ N') (u : ZMod N → ℂ) :
    charPair ψ (pullback hNN u) = ∑ a : (ZMod N)ˣ, u a / (fibreSize hNN : ℂ) *
      ∑ b ∈ unitsFibre hNN a, ψ (b : ZMod N') := by
  unfold charPair pullback
  have e : ∀ b : ZMod N',
      ψ b * (if IsUnit b then u (b.cast : ZMod N) / (fibreSize hNN : ℂ) else 0) =
      if IsUnit b then ψ b * (u (b.cast : ZMod N) / (fibreSize hNN : ℂ)) else 0 := by
    intro b; split_ifs <;> ring
  simp_rw [e]
  rw [sum_ite_isUnit, sum_units_eq_sum_fibres hNN]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [cast_of_mem_unitsFibre hNN hb]
  ring

/-- **Characters that do not factor through `N` do not see a pulled-back vector.** -/
theorem charPair_pullback_of_not_factorsThrough {ψ : DirichletCharacter ℂ N'}
    (hψ : ¬ ψ.FactorsThrough N) (u : ZMod N → ℂ) : charPair ψ (pullback hNN u) = 0 := by
  rw [charPair_pullback_eq]
  exact Finset.sum_eq_zero fun a _ => by rw [sum_unitsFibre_eq_zero hNN hψ a, mul_zero]

/-- **Induced characters see the original pairing.** -/
theorem charPair_changeLevel_pullback (ξ : DirichletCharacter ℂ N) (u : ZMod N → ℂ) :
    charPair (DirichletCharacter.changeLevel hNN ξ) (pullback hNN u) = charPair ξ u := by
  rw [charPair_pullback_eq]
  have hm : (fibreSize hNN : ℂ) ≠ 0 := by exact_mod_cast (fibreSize_pos hNN).ne'
  have hfib : ∀ a : (ZMod N)ˣ, ∑ b ∈ unitsFibre hNN a,
      (DirichletCharacter.changeLevel hNN ξ) (b : ZMod N') = ξ a * (fibreSize hNN : ℂ) := by
    intro a
    have e : ∀ b ∈ unitsFibre hNN a, (DirichletCharacter.changeLevel hNN ξ) (b : ZMod N') =
        ξ a := by
      intro b hb
      rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, cast_of_mem_unitsFibre hNN hb]
    rw [Finset.sum_congr rfl e, Finset.sum_const, card_unitsFibre, nsmul_eq_mul, mul_comm]
  simp_rw [hfib]
  unfold charPair
  have e2 : ∀ b : ZMod N, ξ b * u b = if IsUnit b then ξ b * u b else 0 := by
    intro b
    split_ifs with hb
    · rfl
    · rw [MulChar.map_nonunit ξ hb, zero_mul]
  rw [Finset.sum_congr rfl (fun b _ => e2 b), sum_ite_isUnit]
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp

theorem sum_norm_pullback_le (u : ZMod N → ℂ) :
    ∑ b, ‖pullback hNN u b‖ ≤ ∑ a, ‖u a‖ := by
  have hm : (0 : ℝ) < fibreSize hNN := by exact_mod_cast fibreSize_pos hNN
  have e : ∀ b : ZMod N', ‖pullback hNN u b‖ =
      if IsUnit b then ‖u (b.cast : ZMod N)‖ / (fibreSize hNN : ℝ) else 0 := by
    intro b
    unfold pullback
    split_ifs
    · rw [norm_div, Complex.norm_natCast]
    · exact norm_zero
  have e' : ∑ b, ‖pullback hNN u b‖ = ∑ a : (ZMod N)ˣ, ‖u a‖ := by
    simp_rw [e]
    have : ∑ b : ZMod N', (if IsUnit b then ‖u (b.cast : ZMod N)‖ / (fibreSize hNN : ℝ) else 0) =
        ∑ b : (ZMod N')ˣ, ‖u ((b : ZMod N').cast : ZMod N)‖ / (fibreSize hNN : ℝ) := by
      classical
      rw [← Finset.sum_filter]
      symm
      refine Finset.sum_nbij' (fun b => (b : ZMod N'))
        (fun b => if h : IsUnit b then h.unit else 1) ?_ ?_ ?_ ?_ ?_
      · intro b _; simp
      · intro b _; simp
      · intro b _; simp
      · intro b hb
        have hb' : IsUnit b := (Finset.mem_filter.mp hb).2
        simp [hb']
      · intro b _; rfl
    rw [this]
    classical
    rw [(Finset.sum_fiberwise Finset.univ (ZMod.unitsMap hNN) _).symm]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e3 : ∀ b ∈ Finset.univ.filter (fun b => ZMod.unitsMap hNN b = a),
        ‖u ((b : ZMod N').cast : ZMod N)‖ / (fibreSize hNN : ℝ) = ‖u a‖ / (fibreSize hNN : ℝ) := by
      intro b hb
      rw [cast_of_mem_unitsFibre hNN hb]
    rw [Finset.sum_congr rfl e3, Finset.sum_const]
    have hc : (Finset.univ.filter fun b => ZMod.unitsMap hNN b = a).card = fibreSize hNN :=
      card_unitsFibre hNN a
    rw [hc, nsmul_eq_mul]
    field_simp
  rw [e']
  classical
  calc ∑ a : (ZMod N)ˣ, ‖u a‖ = ∑ b ∈ Finset.univ.filter (fun b : ZMod N => IsUnit b), ‖u b‖ := by
        refine Finset.sum_nbij' (fun b => (b : ZMod N))
          (fun b => if h : IsUnit b then h.unit else 1) ?_ ?_ ?_ ?_ ?_
        · intro b _; simp
        · intro b _; simp
        · intro b _; simp
        · intro b hb
          have hb' : IsUnit b := (Finset.mem_filter.mp hb).2
          simp [hb']
        · intro b _; rfl
    _ ≤ ∑ b, ‖u b‖ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => norm_nonneg _

omit [NeZero N] in
theorem norm_pullback_le (u : ZMod N → ℂ) {K : ℝ} (hK : ∀ a, ‖u a‖ ≤ K) (hK0 : 0 ≤ K)
    (b : ZMod N') : ‖pullback hNN u b‖ ≤ K := by
  have hm : (1 : ℝ) ≤ fibreSize hNN := by exact_mod_cast fibreSize_pos hNN
  unfold pullback
  split_ifs
  · rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
    nlinarith [hK ((b.cast : ZMod N))]
  · rw [norm_zero]; exact hK0

end Fibres

/-! ## Realization at a level -/

/-- Large prime sets in a unit class avoiding the primes `≤ P₀`. -/
theorem exists_finset_primeRecip_gt_above {M : ℕ} [NeZero M] {a : ZMod M} (ha : IsUnit a) (R : ℝ)
    (P₀ : ℕ) : ∃ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ (p : ZMod M) = a ∧ P₀ < p) ∧
      R < ∑ p ∈ T, ((p : ℝ))⁻¹ := by
  classical
  obtain ⟨T, hT, hsum⟩ := exists_finset_primeRecip_gt ha (R + P₀ + 1)
  refine ⟨T.filter (fun p => P₀ < p), fun p hp => ?_, ?_⟩
  · obtain ⟨hpT, hpP⟩ := Finset.mem_filter.mp hp
    exact ⟨(hT p hpT).1, (hT p hpT).2, hpP⟩
  · have hsplit := Finset.sum_filter_add_sum_filter_not T (fun p => P₀ < p)
      (fun p => ((p : ℝ))⁻¹)
    have hsmall : ∑ p ∈ T.filter (fun p => ¬ P₀ < p), ((p : ℝ))⁻¹ ≤ P₀ + 1 := by
      have hsub : T.filter (fun p => ¬ P₀ < p) ⊆ Finset.range (P₀ + 1) := by
        intro p hp
        have := (Finset.mem_filter.mp hp).2
        exact Finset.mem_range.mpr (by omega)
      have hb : ∀ p ∈ T.filter (fun p => ¬ P₀ < p), ((p : ℝ))⁻¹ ≤ 1 := by
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by
          exact_mod_cast (hT p (Finset.mem_filter.mp hp).1).1.one_lt.le
        exact inv_le_one_of_one_le₀ hp1
      calc ∑ p ∈ T.filter (fun p => ¬ P₀ < p), ((p : ℝ))⁻¹
          ≤ ((T.filter (fun p => ¬ P₀ < p)).card : ℝ) * 1 := by
            have := Finset.sum_le_card_nsmul _ _ _ hb
            rwa [nsmul_eq_mul] at this
        _ ≤ ((Finset.range (P₀ + 1)).card : ℝ) * 1 := by
            gcongr
        _ = P₀ + 1 := by simp
    linarith

/-- **Realization of a pairing vector by primes.** For an affine family `u₀ + t w` on `ℤ/M` with
entries bounded by `K` on `|t| ≤ 1` and any `R > 0`, there are `σ > 1`, a finite set `S` of primes
`p > P₀` in the unit classes mod `M`, and values `z_t(p)`, holomorphic in `t`, with
`Σ_p ψ(p) z_t(p) = ⟨ψ, u₀ + t w⟩` for every character `ψ` mod `M`, `|z_t(p)| ≤ (K/R) p^{−σ}` and
`Σ_p |z_t(p)| ≤ Σ_a |(u₀ + t w)(a)|`. -/
theorem exists_realization {M : ℕ} [NeZero M] (u₀ w : ZMod M → ℂ) {K R : ℝ}
    (hK : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ a, ‖(u₀ + t • w) a‖ ≤ K) (hRpos : 0 < R) (P₀ : ℕ) :
    ∃ σ : ℝ, 1 < σ ∧ ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ IsUnit (p : ZMod M) ∧ P₀ < p) ∧
      ∃ z : ℂ → ℕ → ℂ,
        (∀ t : ℂ, ‖t‖ ≤ 1 → ∀ p ∈ S, ‖z t p‖ ≤ K / R * ((p : ℝ)) ^ (-σ)) ∧
        (∀ t : ℂ, ∑ p ∈ S, ‖z t p‖ ≤ ∑ a, ‖(u₀ + t • w) a‖) ∧
        (∀ (t : ℂ) (ψ : DirichletCharacter ℂ M),
          ∑ p ∈ S, ψ p * z t p = charPair ψ (u₀ + t • w)) ∧
        (∀ p, Differentiable ℂ (fun t => z t p)) ∧
        (∀ p ∈ S, ((p : ℝ)) ^ (-σ) ≤ 1) := by
  classical
  have hS₀ : ∀ a : ZMod M, ∃ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ (p : ZMod M) = a ∧ P₀ < p) ∧
      (IsUnit a → R + 1 < ∑ p ∈ T, ((p : ℝ))⁻¹) := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨T, hT, hsum⟩ := exists_finset_primeRecip_gt_above ha (R + 1) P₀
      exact ⟨T, hT, fun _ => hsum⟩
    · exact ⟨∅, by simp, fun h => absurd h ha⟩
  choose T hTp hTsum using hS₀
  set S : Finset ℕ := Finset.univ.filter (fun a : ZMod M => IsUnit a) |>.biUnion T with hS
  have hSmem : ∀ p ∈ S, p.Prime ∧ IsUnit (p : ZMod M) ∧ P₀ < p := by
    intro p hp
    obtain ⟨a, ha, hpa⟩ := Finset.mem_biUnion.mp hp
    have h' := hTp a p hpa
    exact ⟨h'.1, h'.2.1 ▸ (Finset.mem_filter.mp ha).2, h'.2.2⟩
  have hcont : ∀ a : ZMod M, ∀ᶠ σ in 𝓝 (1 : ℝ),
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
  set Rf : ZMod M → ℝ := fun a =>
    ∑ p ∈ S.filter (fun p : ℕ => (p : ZMod M) = a), ((p : ℝ)) ^ (-σ) with hRf
  have hRfR : ∀ a : ZMod M, IsUnit a → R < Rf a := by
    intro a ha
    refine (hσall a ha).trans_le (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by
      positivity)
    intro p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr
      ⟨Finset.mem_univ a, ha⟩, hp⟩, (hTp a p hp).2.1⟩
  have hRf0 : ∀ a : ZMod M, 0 ≤ Rf a := fun a => Finset.sum_nonneg fun _ _ => by positivity
  have hpσ : ∀ p ∈ S, 0 < ((p : ℝ)) ^ (-σ) ∧ ((p : ℝ)) ^ (-σ) ≤ 1 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hSmem p hp).1.one_lt.le
    exact ⟨Real.rpow_pos_of_pos (by linarith) _,
      Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)⟩
  set zt : ℂ → ℕ → ℂ := fun t p =>
    (u₀ + t • w) (p : ZMod M) * ((((p : ℝ)) ^ (-σ) / Rf (p : ZMod M) : ℝ) : ℂ) with hzt
  refine ⟨σ, hσ1', S, hSmem, zt, ?_, ?_, ?_, ?_, fun p hp => (hpσ p hp).2⟩
  · intro t ht0 p hp
    have hRp := hRfR _ (hSmem p hp).2.1
    have hRp0 : 0 < Rf (p : ZMod M) := hRpos.trans hRp
    simp only [hzt, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (div_nonneg (hpσ p hp).1.le hRp0.le)]
    have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK t ht0 (p : ZMod M))
    calc ‖(u₀ + t • w) (p : ZMod M)‖ * (((p : ℝ)) ^ (-σ) / Rf (p : ZMod M))
        ≤ K * (((p : ℝ)) ^ (-σ) / R) := by
          refine mul_le_mul (hK t ht0 _) ?_ (by positivity) hK0
          exact div_le_div_of_nonneg_left (hpσ p hp).1.le hRpos hRp.le
      _ = K / R * ((p : ℝ)) ^ (-σ) := by ring
  · intro t
    rw [← Finset.sum_fiberwise S (fun p => (p : ZMod M))]
    refine Finset.sum_le_sum fun a _ => ?_
    by_cases hS0 : Rf a = 0
    · have : ∀ p ∈ S.filter (fun p : ℕ => (p : ZMod M) = a), ‖zt t p‖ = 0 := by
        intro p hp
        have hpa : (p : ZMod M) = a := (Finset.mem_filter.mp hp).2
        simp only [hzt, hpa, hS0, div_zero, Complex.ofReal_zero, mul_zero, norm_zero]
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero]; exact norm_nonneg _
    · have hRa : 0 < Rf a := lt_of_le_of_ne (hRf0 a) (Ne.symm hS0)
      have e : ∀ p ∈ S.filter (fun p : ℕ => (p : ZMod M) = a), ‖zt t p‖ =
          ‖(u₀ + t • w) a‖ * (((p : ℝ)) ^ (-σ) / Rf a) := by
        intro p hp
        have hpa : (p : ZMod M) = a := (Finset.mem_filter.mp hp).2
        have hp' := (hpσ p (Finset.mem_filter.mp hp).1).1
        simp only [hzt, hpa, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (div_nonneg hp'.le hRa.le)]
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← Finset.sum_div]
      have : ∑ p ∈ S.filter (fun p : ℕ => (p : ZMod M) = a), ((p : ℝ)) ^ (-σ) = Rf a := rfl
      rw [this, div_self hRa.ne', mul_one]
  · intro t χ
    rw [← Finset.sum_fiberwise S (fun p => (p : ZMod M))]
    unfold charPair
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : IsUnit a
    · have hRa : 0 < Rf a := hRpos.trans (hRfR a ha)
      have e : ∀ p ∈ S.filter (fun p : ℕ => (p : ZMod M) = a), χ p * zt t p =
          χ a * (u₀ + t • w) a * ((((p : ℝ)) ^ (-σ) : ℝ) : ℂ) / ((Rf a : ℝ) : ℂ) := by
        intro p hp
        have hpa : (p : ZMod M) = a := (Finset.mem_filter.mp hp).2
        simp only [hzt, hpa]
        push_cast
        ring
      rw [Finset.sum_congr rfl e, ← Finset.sum_div, ← Finset.mul_sum]
      have hsum : ∑ p ∈ S.filter (fun p : ℕ => (p : ZMod M) = a),
          ((((p : ℝ)) ^ (-σ) : ℝ) : ℂ) = ((Rf a : ℝ) : ℂ) := by
        simp only [hRf]; push_cast; rfl
      rw [hsum]
      have : ((Rf a : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hRa.ne'
      field_simp
    · have hχ : χ a = 0 := MulChar.map_nonunit χ ha
      rw [hχ, zero_mul]
      refine Finset.sum_eq_zero fun p hp => ?_
      have hpa : (p : ZMod M) = a := (Finset.mem_filter.mp hp).2
      exact absurd (hpa ▸ (hSmem p (Finset.mem_filter.mp hp).1).2.1) ha
  · intro p
    simp only [hzt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop

/-! ## The two-level zero -/

theorem changeLevel_natCast_of_isUnit {N N' : ℕ} (hNN : N ∣ N') (ξ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : IsUnit (p : ZMod N')) :
    (DirichletCharacter.changeLevel hNN ξ) (p : ZMod N') = ξ (p : ZMod N) := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ξ hNN hp.unit
  rw [IsUnit.unit_spec] at h
  rw [h, ZMod.cast_natCast hNN]

/-- **The level-`N` model** of `exists_charProduct_zero`: vectors `u₀, w` on `ℤ/N` with
`|Σ_χ C(χ) e^{⟨χ, u₀ + t w⟩} − C(χ₁)(1 − e^t)| ≤ |C(χ₁)|/48` for every `t`. -/
theorem exists_twoLevel_model {N : ℕ} [NeZero N] {C : DirichletCharacter ℂ N → ℂ}
    {χ₁ χ₂ : DirichletCharacter ℂ N} (h12 : χ₁ ≠ χ₂) (h1 : C χ₁ ≠ 0) (h2 : C χ₂ ≠ 0) :
    ∃ u₀ w : ZMod N → ℂ, ∀ t : ℂ,
      ‖∑ χ, C χ * cexp (charPair χ (u₀ + t • w)) - C χ₁ * (1 - cexp t)‖ ≤ ‖C χ₁‖ / 48 := by
  classical
  set c₁ : ℝ := ‖C χ₁‖ with hc₁
  have hc₁pos : 0 < c₁ := norm_pos_iff.mpr h1
  set A : ℝ := ∑ χ, ‖C χ‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, Real.exp (-R') * A ≤ c₁ / 48 := by
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
  have hχ₁o : χ₁ ∉ others := by simp [hothers]
  have hχ₂o : χ₂ ∉ others := by simp [hothers]
  have hMeq : ∀ t : ℂ, ∑ χ, C χ * cexp (charPair χ (u₀ + t • w)) = C χ₁ * (1 - cexp t) +
      ∑ χ ∈ others, C χ * cexp (-((R' : ℝ) : ℂ)) := by
    intro t
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
  refine ⟨u₀, w, fun t => ?_⟩
  rw [hMeq, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ χ ∈ others, ‖C χ * cexp (-((R' : ℝ) : ℂ))‖ =
        ∑ χ ∈ others, ‖C χ‖ * Real.exp (-R') := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [norm_mul, Complex.norm_exp]; simp
    _ ≤ ∑ χ, ‖C χ‖ * Real.exp (-R') :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => by positivity
    _ = Real.exp (-R') * A := by rw [hA, ← Finset.sum_mul, mul_comm]
    _ ≤ c₁ / 48 := hR'

/-- **Product estimates for small prime values.** If `|z_p| ≤ ε ≤ ½`, `Σ|z_p| ≤ K` and
`εK ≤ ½`, then for `|h| ≤ 1` the product `Π(1 − h_p z_p)^{−1}` is within
`|exp Σ h_p z_p|·2εK` of `exp Σ h_p z_p`, and both are at most `2e^K`. -/
theorem prod_inv_estimates {S : Finset ℕ} {z h : ℕ → ℂ} {ε K : ℝ}
    (hh : ∀ p, ‖h p‖ ≤ 1) (hz : ∀ p ∈ S, ‖z p‖ ≤ ε) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hsum : ∑ p ∈ S, ‖z p‖ ≤ K) (hεK : ε * K ≤ 1 / 2) :
    ‖∏ p ∈ S, (1 - h p * z p)⁻¹ - cexp (∑ p ∈ S, h p * z p)‖ ≤
        ‖cexp (∑ p ∈ S, h p * z p)‖ * (2 * (ε * K)) ∧
      ‖cexp (∑ p ∈ S, h p * z p)‖ ≤ Real.exp K ∧
      ‖∏ p ∈ S, (1 - h p * z p)⁻¹‖ ≤ 2 * Real.exp K := by
  have hn : ∀ p, ‖h p * z p‖ ≤ ‖z p‖ := fun p => by
    rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hh p)
  have hw : ∀ p ∈ S, ‖h p * z p‖ ≤ 1 / 2 := fun p hp => ((hn p).trans (hz p hp)).trans hε
  have hsq : ∑ p ∈ S, ‖h p * z p‖ ^ 2 ≤ ε * K := by
    calc ∑ p ∈ S, ‖h p * z p‖ ^ 2 ≤ ∑ p ∈ S, ε * ‖z p‖ := by
          refine Finset.sum_le_sum fun p hp => ?_
          calc ‖h p * z p‖ ^ 2 ≤ ‖z p‖ ^ 2 := by gcongr; exact hn p
            _ = ‖z p‖ * ‖z p‖ := sq _
            _ ≤ ε * ‖z p‖ := mul_le_mul_of_nonneg_right (hz p hp) (norm_nonneg _)
      _ = ε * ∑ p ∈ S, ‖z p‖ := by rw [Finset.mul_sum]
      _ ≤ ε * K := mul_le_mul_of_nonneg_left hsum hε0
  have h1 : ‖∏ p ∈ S, (1 - h p * z p)⁻¹ - cexp (∑ p ∈ S, h p * z p)‖ ≤
      ‖cexp (∑ p ∈ S, h p * z p)‖ * (2 * (ε * K)) :=
    (norm_prod_inv_sub_exp_le S (fun p => h p * z p) hw (hsq.trans (by linarith))).trans
      (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _))
  have h2 : ‖cexp (∑ p ∈ S, h p * z p)‖ ≤ Real.exp K := by
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun p _ => hn p).trans hsum)
  refine ⟨h1, h2, ?_⟩
  have h4 := norm_sub_norm_le (∏ p ∈ S, (1 - h p * z p)⁻¹) (cexp (∑ p ∈ S, h p * z p))
  have h5 : ‖cexp (∑ p ∈ S, h p * z p)‖ * (2 * (ε * K)) ≤ ‖cexp (∑ p ∈ S, h p * z p)‖ :=
    mul_le_of_le_one_right (norm_nonneg _) (by linarith)
  linarith

/-- Products `Π(1 − h_p z_p(t))^{−1}` are holomorphic where the factors stay away from `0`. -/
theorem differentiableAt_prod_inv {S : Finset ℕ} {zt : ℂ → ℕ → ℂ} {h : ℕ → ℂ} {t : ℂ}
    (hd : ∀ p, Differentiable ℂ (fun t => zt t p)) (hs : ∀ p ∈ S, ‖h p * zt t p‖ ≤ 1 / 2) :
    DifferentiableAt ℂ (fun t' => ∏ p ∈ S, (1 - h p * zt t' p)⁻¹) t := by
  refine DifferentiableAt.fun_finsetProd fun p hp => ?_
  have hne : 1 - h p * zt t p ≠ 0 := by
    intro h0
    have h1 : h p * zt t p = 1 := by linear_combination -h0
    have := hs p hp
    rw [h1, norm_one] at this
    norm_num at this
  exact ((differentiableAt_const _).sub ((differentiableAt_const _).mul
    ((hd p).differentiableAt))).inv hne

/-- The size of the realization: `R` with `K ≤ R/2`, `K·Kt ≤ R/4` and
`A e^{Kt}·2(K·Kt/R) ≤ c/48`. -/
theorem exists_realization_size {A Kt K c : ℝ} (hA : 0 ≤ A) (hKt : 0 ≤ Kt) (hK : 1 ≤ K)
    (hc : 0 < c) : ∃ R : ℝ, 0 < R ∧ K / R ≤ 1 / 2 ∧ K / R * Kt ≤ 1 / 4 ∧
      A * Real.exp Kt * (2 * (K / R * Kt)) ≤ c / 48 := by
  set B : ℝ := (A + 1) * Real.exp Kt * 2 * (K * Kt) * 48 / c with hB
  have hB0 : 0 ≤ B := by positivity
  have hKKt : 0 ≤ K * Kt := by positivity
  set R : ℝ := 2 * K + 4 * (K * Kt) + B + 1 with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  refine ⟨R, hRpos, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hRpos]; rw [hR]; linarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]; rw [hR]; linarith
  · have hBR : B ≤ R := by rw [hR]; linarith
    rw [hB, div_le_iff₀ hc] at hBR
    have hAle : A * Real.exp Kt * (2 * (K * Kt)) ≤ (A + 1) * Real.exp Kt * (2 * (K * Kt)) := by
      gcongr; linarith
    rw [show A * Real.exp Kt * (2 * (K / R * Kt)) = A * Real.exp Kt * (2 * (K * Kt)) / R by
      field_simp, div_le_iff₀ hRpos]
    nlinarith

/-- **Two-level zero planting with an abstract far part.** The far part `Φ(S, z)` may be any
functional with `|Φ(S, v)| ≤ η e^{2Σ_S|v_p|}` for `v` supported on `S` with `|v_p| ≤ ½`, which is
holomorphic along holomorphic families of such vectors. -/
theorem exists_twoLevel_zero_of_far {N : ℕ} [NeZero N] {C : DirichletCharacter ℂ N → ℂ}
    {χ₁ χ₂ : DirichletCharacter ℂ N} (h12 : χ₁ ≠ χ₂) (h1 : C χ₁ ≠ 0) (h2 : C χ₂ ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ (N' : ℕ) [NeZero N'] (_ : N ∣ N') (P₀ : ℕ)
      (D : DirichletCharacter ℂ N' → ℂ), (∀ ψ, D ψ ≠ 0 → ¬ ψ.FactorsThrough N) →
      ∑ ψ, ‖D ψ‖ ≤ ‖C χ₁‖ / 96 →
      ∀ Φ : Finset ℕ → (ℕ → ℂ) → ℂ,
        (∀ (S : Finset ℕ) (v : ℕ → ℂ), (∀ p, p ∉ S → v p = 0) → (∀ p ∈ S, ‖v p‖ ≤ 1 / 2) →
          ‖Φ S v‖ ≤ η * Real.exp (2 * ∑ p ∈ S, ‖v p‖)) →
        (∀ (S : Finset ℕ) (zt : ℂ → ℕ → ℂ) (U : Set ℂ), IsOpen U →
          (∀ p, Differentiable ℂ (fun t => zt t p)) → (∀ t ∈ U, ∀ p, p ∉ S → zt t p = 0) →
          (∀ t ∈ U, ∀ p ∈ S, ‖zt t p‖ ≤ 1 / 2) → DifferentiableOn ℂ (fun t => Φ S (zt t)) U) →
        ∃ σ : ℝ, 1 < σ ∧ ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ IsUnit (p : ZMod N') ∧ P₀ < p) ∧
          ∃ z : ℕ → ℂ, (∀ p ∈ S, ‖z p‖ ≤ ((p : ℝ)) ^ (-σ)) ∧ (∀ p, p ∉ S → z p = 0) ∧
            ∑ ξ, C ξ * ∏ p ∈ S, (1 - ξ p * z p)⁻¹ +
              ∑ ψ, D ψ * ∏ p ∈ S, (1 - ψ p * z p)⁻¹ + Φ S z = 0 := by
  classical
  set c₁ : ℝ := ‖C χ₁‖ with hc₁
  have hc₁pos : 0 < c₁ := norm_pos_iff.mpr h1
  set A : ℝ := ∑ χ, ‖C χ‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨u₀, w, hMclose⟩ := exists_twoLevel_model h12 h1 h2
  set Kt : ℝ := ∑ a, (‖u₀ a‖ + ‖w a‖) with hKt
  have hKt0 : 0 ≤ Kt := Finset.sum_nonneg fun _ _ => by positivity
  have hu_entry : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ a, ‖(u₀ + t • w) a‖ ≤ ‖u₀ a‖ + ‖w a‖ := by
    intro t ht0 a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) ht0
  have hu_bound : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ a, ‖(u₀ + t • w) a‖ ≤ Kt := by
    intro t ht0 a
    refine (hu_entry t ht0 a).trans ?_
    exact Finset.single_le_sum (f := fun b => ‖u₀ b‖ + ‖w b‖) (fun _ _ => by positivity)
      (Finset.mem_univ a)
  have hsumu : ∀ t : ℂ, ‖t‖ ≤ 1 → ∑ a, ‖(u₀ + t • w) a‖ ≤ Kt :=
    fun t ht0 => Finset.sum_le_sum fun a _ => hu_entry t ht0 a
  obtain ⟨R, hRpos, hKR, hKRKt, hRerr⟩ :=
    exists_realization_size hA0 hKt0 (show (1 : ℝ) ≤ Kt + 1 by linarith) hc₁pos
  refine ⟨c₁ / (48 * Real.exp (2 * Kt)), by positivity, ?_⟩
  intro N' _ hNN P₀ D hD hDsum Φ hΦb hΦd
  /- The pulled-back family at level `N'`. -/
  have hpb : ∀ t : ℂ, pullback hNN u₀ + t • pullback hNN w = pullback hNN (u₀ + t • w) :=
    fun t => (pullback_add_smul hNN u₀ w t).symm
  have hUbound : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ b, ‖(pullback hNN u₀ + t • pullback hNN w) b‖ ≤ Kt + 1 := by
    intro t ht0 b
    rw [hpb]
    exact (norm_pullback_le hNN _ (hu_bound t ht0) hKt0 b).trans (by linarith)
  obtain ⟨σ, hσ1, S, hSmem, zt, hzt_norm, hzsum', hpair', hzd, hpσle⟩ :=
    exists_realization (pullback hNN u₀) (pullback hNN w) hUbound hRpos P₀
  have hpσpos : ∀ p ∈ S, 0 < ((p : ℝ)) ^ (-σ) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hSmem p hp).1.one_lt.le
    exact Real.rpow_pos_of_pos (by linarith) _
  set ε : ℝ := (Kt + 1) / R with hε
  have hzε : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ p ∈ S, ‖zt t p‖ ≤ ε := fun t ht0 p hp =>
    (hzt_norm t ht0 p hp).trans (mul_le_of_le_one_right (by positivity) (hpσle p hp))
  have hzsum : ∀ t : ℂ, ‖t‖ ≤ 1 → ∑ p ∈ S, ‖zt t p‖ ≤ Kt := by
    intro t ht0
    refine (hzsum' t).trans ?_
    rw [hpb]
    exact (sum_norm_pullback_le hNN _).trans (hsumu t ht0)
  have hεK : ε * Kt ≤ 1 / 2 := by linarith
  have hE := fun (h : ℕ → ℂ) (hh : ∀ p, ‖h p‖ ≤ 1) (t : ℂ) (ht0 : ‖t‖ ≤ 1) =>
    prod_inv_estimates (S := S) (z := zt t) hh (hzε t ht0) (by positivity) hKR (hzsum t ht0) hεK
  have hsmall : ∀ (h : ℕ → ℂ), (∀ p, ‖h p‖ ≤ 1) → ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ p ∈ S,
      ‖h p * zt t p‖ ≤ 1 / 2 := by
    intro h hh t ht0 p hp
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hh p)).trans ((hzε t ht0 p hp).trans hKR)
  have hξle : ∀ ξ : DirichletCharacter ℂ N, ∀ p : ℕ, ‖ξ p‖ ≤ 1 := fun ξ p =>
    DirichletCharacter.norm_le_one ξ _
  have hψle : ∀ ψ : DirichletCharacter ℂ N', ∀ p : ℕ, ‖ψ p‖ ≤ 1 := fun ψ p =>
    DirichletCharacter.norm_le_one ψ _
  have hpairN : ∀ (t : ℂ) (ξ : DirichletCharacter ℂ N),
      ∑ p ∈ S, ξ p * zt t p = charPair ξ (u₀ + t • w) := by
    intro t ξ
    have e' : ∀ p ∈ S, ξ p * zt t p = (DirichletCharacter.changeLevel hNN ξ) p * zt t p := by
      intro p hp
      rw [changeLevel_natCast_of_isUnit hNN ξ (hSmem p hp).2.1]
    rw [Finset.sum_congr rfl e', hpair', hpb, charPair_changeLevel_pullback]
  /- The three parts. -/
  set Tc : ℂ → ℂ := fun t => ∑ ξ, C ξ * ∏ p ∈ S, (1 - ξ p * zt t p)⁻¹ with hTc
  set Td : ℂ → ℂ := fun t => ∑ ψ, D ψ * ∏ p ∈ S, (1 - ψ p * zt t p)⁻¹ with hTd
  set zS : ℂ → ℕ → ℂ := fun t p => if p ∈ S then zt t p else 0 with hzS
  set Te : ℂ → ℂ := fun t => Φ S (zS t) with hTe
  have hTcM : ∀ t : ℂ, ‖t‖ ≤ 1 →
      ‖Tc t - ∑ χ, C χ * cexp (charPair χ (u₀ + t • w))‖ ≤ c₁ / 48 := by
    intro t ht0
    have hterm : ∀ ξ : DirichletCharacter ℂ N,
        ‖C ξ * ∏ p ∈ S, (1 - ξ p * zt t p)⁻¹ - C ξ * cexp (charPair ξ (u₀ + t • w))‖ ≤
          ‖C ξ‖ * (Real.exp Kt * (2 * (ε * Kt))) := by
      intro ξ
      rw [← mul_sub, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      obtain ⟨ha, hb, -⟩ := hE (fun p => ξ p) (hξle ξ) t ht0
      rw [hpairN] at ha hb
      exact ha.trans (mul_le_mul_of_nonneg_right hb (by positivity))
    calc ‖Tc t - ∑ χ, C χ * cexp (charPair χ (u₀ + t • w))‖ =
          ‖∑ ξ, (C ξ * ∏ p ∈ S, (1 - ξ p * zt t p)⁻¹ -
            C ξ * cexp (charPair ξ (u₀ + t • w)))‖ := by
          simp only [hTc, Finset.sum_sub_distrib]
      _ ≤ ∑ ξ, ‖C ξ‖ * (Real.exp Kt * (2 * (ε * Kt))) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => hterm ξ)
      _ = A * Real.exp Kt * (2 * (ε * Kt)) := by rw [← Finset.sum_mul, ← hA]; ring
      _ ≤ c₁ / 48 := hRerr
  have hTdle : ∀ t : ℂ, ‖t‖ ≤ 1 → ‖Td t‖ ≤ c₁ / 48 := by
    intro t ht0
    have hterm : ∀ ψ : DirichletCharacter ℂ N',
        ‖D ψ * ∏ p ∈ S, (1 - ψ p * zt t p)⁻¹‖ ≤ 2 * ‖D ψ‖ := by
      intro ψ
      by_cases hψ0 : D ψ = 0
      · rw [hψ0, zero_mul, norm_zero, mul_zero]
      · have hzero : ∑ p ∈ S, ψ p * zt t p = 0 := by
          rw [hpair', hpb, charPair_pullback_of_not_factorsThrough hNN (hD ψ hψ0)]
        obtain ⟨ha, -, -⟩ := hE (fun p => ψ p) (hψle ψ) t ht0
        rw [hzero, Complex.exp_zero, norm_one, one_mul] at ha
        have h4 := norm_sub_norm_le (∏ p ∈ S, (1 - ψ p * zt t p)⁻¹) (1 : ℂ)
        rw [norm_one] at h4
        have hb : ‖∏ p ∈ S, (1 - ψ p * zt t p)⁻¹‖ ≤ 2 := by linarith only [h4, ha, hεK]
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    calc ‖Td t‖ ≤ ∑ ψ, 2 * ‖D ψ‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun ψ _ => hterm ψ)
      _ = 2 * ∑ ψ, ‖D ψ‖ := by rw [Finset.mul_sum]
      _ ≤ c₁ / 48 := by linarith only [hDsum, hc₁]
  have hzS_supp : ∀ t : ℂ, ∀ p, p ∉ S → zS t p = 0 := fun t p hp => by
    simp only [hzS, if_neg hp]
  have hzS_eq : ∀ t : ℂ, ∀ p ∈ S, zS t p = zt t p := fun t p hp => by
    simp only [hzS, if_pos hp]
  have hzS_half : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ p ∈ S, ‖zS t p‖ ≤ 1 / 2 := fun t ht0 p hp => by
    rw [hzS_eq t p hp]; exact (hzε t ht0 p hp).trans hKR
  have hTele : ∀ t : ℂ, ‖t‖ ≤ 1 → ‖Te t‖ ≤ c₁ / 48 := by
    intro t ht0
    have hb := hΦb S (zS t) (hzS_supp t) (hzS_half t ht0)
    have hsumS : ∑ p ∈ S, ‖zS t p‖ ≤ Kt := by
      rw [Finset.sum_congr rfl fun p hp => by rw [hzS_eq t p hp]]
      exact hzsum t ht0
    calc ‖Te t‖ ≤ c₁ / (48 * Real.exp (2 * Kt)) * Real.exp (2 * ∑ p ∈ S, ‖zS t p‖) := hb
      _ ≤ c₁ / (48 * Real.exp (2 * Kt)) * Real.exp (2 * Kt) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      _ = c₁ / 48 := by field_simp
  /- Holomorphy on the unit disc. -/
  have hball1 : ∀ t ∈ ball (0 : ℂ) 1, ‖t‖ ≤ 1 := fun t ht => (mem_ball_zero_iff.mp ht).le
  have hTedOn : DifferentiableOn ℂ Te (ball (0 : ℂ) 1) := by
    refine hΦd S zS (ball (0 : ℂ) 1) isOpen_ball (fun p => ?_) (fun t _ p hp => hzS_supp t p hp)
      (fun t ht p hp => hzS_half t (hball1 t ht) p hp)
    by_cases hp : p ∈ S
    · simp only [hzS, if_pos hp]; exact hzd p
    · simp only [hzS, if_neg hp]; exact differentiable_const _
  set Tf : ℂ → ℂ := fun t => Tc t + Td t + Te t with hTf
  have hTfd : ∀ t ∈ ball (0 : ℂ) 1, DifferentiableAt ℂ Tf t := by
    intro t ht
    have ht0 := hball1 t ht
    have hc : DifferentiableAt ℂ Tc t :=
      DifferentiableAt.fun_sum fun ξ _ => (differentiableAt_const _).mul
        (differentiableAt_prod_inv hzd (hsmall (fun p => ξ p) (hξle ξ) t ht0))
    have hd : DifferentiableAt ℂ Td t :=
      DifferentiableAt.fun_sum fun ψ _ => (differentiableAt_const _).mul
        (differentiableAt_prod_inv hzd (hsmall (fun p => ψ p) (hψle ψ) t ht0))
    have he' : DifferentiableAt ℂ Te t := hTedOn.differentiableAt (isOpen_ball.mem_nhds ht)
    exact (hc.add hd).add he'
  /- The zero. -/
  set hfun : ℂ → ℂ := fun t => C χ₁ * (1 - cexp t) with hhfun
  set gfun : ℂ → ℂ := fun t => Tf t - hfun t with hgfun
  have hball : closure (ball (0 : ℂ) (1 / 2)) ⊆ ball (0 : ℂ) 1 := by
    rw [closure_ball _ (by norm_num)]
    exact closedBall_subset_ball (by norm_num)
  have hhd : DiffContOnCl ℂ hfun (ball 0 (1 / 2)) :=
    (Differentiable.differentiableOn (by simp only [hhfun]; fun_prop)).diffContOnCl
  have hgd : DiffContOnCl ℂ gfun (ball 0 (1 / 2)) := by
    refine DifferentiableOn.diffContOnCl fun t ht => ?_
    exact ((hTfd t (hball ht)).sub (by simp only [hhfun]; fun_prop)).differentiableWithinAt
  have hup : ∀ t : ℂ, ‖t‖ ≤ 1 → ‖gfun t‖ ≤ c₁ / 12 := by
    intro t ht1
    have e' : gfun t = (Tc t - ∑ χ, C χ * cexp (charPair χ (u₀ + t • w))) +
        (∑ χ, C χ * cexp (charPair χ (u₀ + t • w)) - C χ₁ * (1 - cexp t)) + Td t + Te t := by
      simp only [hgfun, hTf, hhfun]; ring
    rw [e']
    have n1 := norm_add_le ((Tc t - ∑ χ, C χ * cexp (charPair χ (u₀ + t • w))) +
        (∑ χ, C χ * cexp (charPair χ (u₀ + t • w)) - C χ₁ * (1 - cexp t)) + Td t) (Te t)
    have n2 := norm_add_le ((Tc t - ∑ χ, C χ * cexp (charPair χ (u₀ + t • w))) +
        (∑ χ, C χ * cexp (charPair χ (u₀ + t • w)) - C χ₁ * (1 - cexp t))) (Td t)
    have n3 := norm_add_le (Tc t - ∑ χ, C χ * cexp (charPair χ (u₀ + t • w)))
        (∑ χ, C χ * cexp (charPair χ (u₀ + t • w)) - C χ₁ * (1 - cexp t))
    have m1 := hTcM t ht1
    have m2 := hMclose t
    have m3 := hTdle t ht1
    have m4 := hTele t ht1
    linarith only [n1, n2, n3, m1, m2, m3, m4, hc₁]
  obtain ⟨tstar, htstar, hzero⟩ : ∃ t : ℂ, ‖t‖ ≤ 1 ∧ Tf t = 0 := by
    by_cases hg0 : gfun 0 = 0
    · refine ⟨0, by simp, ?_⟩
      have : hfun 0 = 0 := by simp [hhfun]
      have h' : Tf 0 - hfun 0 = 0 := hg0
      rw [this, sub_zero] at h'
      exact h'
    · have hdom : ∀ t ∈ sphere (0 : ℂ) (1 / 2), 3 * ‖gfun t‖ ≤ ‖hfun t‖ := by
        intro t ht
        have htn : ‖t‖ = 1 / 2 := mem_sphere_zero_iff_norm.mp ht
        have ht1 : ‖t‖ ≤ 1 := by rw [htn]; norm_num
        have hlow : c₁ / 4 ≤ ‖hfun t‖ := by
          simp only [hhfun, norm_mul]
          rw [← hc₁, norm_sub_rev]
          have := norm_cexp_sub_one_ge_sub_sq ht1
          rw [htn] at this
          nlinarith
        linarith only [hlow, hup t ht1]
      obtain ⟨t, ht, htz⟩ := exists_zero_of_sphere_domination (by norm_num) hgd hhd
        (by simp [hhfun]) hg0 hdom
      refine ⟨t, ?_, ?_⟩
      · have : ‖t‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp ht
        linarith
      · have : gfun t + hfun t = Tf t := by simp only [hgfun]; ring
        rw [← this]; exact htz
  refine ⟨σ, hσ1, S, hSmem, zS tstar, fun p hp => ?_, hzS_supp tstar, ?_⟩
  · rw [hzS_eq tstar p hp]
    have h1' := hzt_norm tstar htstar p hp
    have h2' := hpσpos p hp
    calc ‖zt tstar p‖ ≤ ε * ((p : ℝ)) ^ (-σ) := h1'
      _ ≤ 1 / 2 * ((p : ℝ)) ^ (-σ) := mul_le_mul_of_nonneg_right hKR h2'.le
      _ ≤ ((p : ℝ)) ^ (-σ) := by linarith
  · have hc : ∀ (h : ℕ → ℂ), ∏ p ∈ S, (1 - h p * zS tstar p)⁻¹ =
        ∏ p ∈ S, (1 - h p * zt tstar p)⁻¹ := fun h =>
      Finset.prod_congr rfl fun p hp => by rw [hzS_eq tstar p hp]
    simp only [hc]
    exact hzero

/-! ## Far parts -/

/-- `(1 − x)^{−1} ≤ e^{2x}` for `0 ≤ x ≤ ½`. -/
theorem inv_one_sub_le_exp_two_mul {x : ℝ} (h0 : 0 ≤ x) (h : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hpos : 0 < 1 - x := by linarith
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  have he := Real.add_one_le_exp (2 * x)
  nlinarith [mul_le_mul_of_nonneg_right he hpos.le, mul_nonneg h0 (by linarith : 0 ≤ 1 - 2 * x)]

/-- `|(1 − w)^{−1}| ≤ e^{2|w|}` and `|(1 − w)^{−1}| ≤ 2` for `|w| ≤ ½`. -/
theorem norm_inv_one_sub_le_exp {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖(1 - w)⁻¹‖ ≤ Real.exp (2 * ‖w‖) ∧ ‖(1 - w)⁻¹‖ ≤ 2 := by
  have h1 : 1 - ‖w‖ ≤ ‖1 - w‖ := by
    have := norm_sub_norm_le (1 : ℂ) w
    rwa [norm_one] at this
  have hpos : 0 < 1 - ‖w‖ := by linarith
  have hle : ‖(1 - w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ hpos h1
  refine ⟨hle.trans (inv_one_sub_le_exp_two_mul (norm_nonneg _) hw), hle.trans ?_⟩
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  linarith

/-- `|Π_{p∈S}(1 − h_p v_p)^{−1}| ≤ e^{2Σ_S|v_p|}` and `≤ 2^{|S|}` when `|h_p| ≤ 1` and
`|v_p| ≤ ½` on `S`. -/
theorem norm_prod_inv_one_sub_le {S : Finset ℕ} {h v : ℕ → ℂ} (hh : ∀ p, ‖h p‖ ≤ 1)
    (hv : ∀ p ∈ S, ‖v p‖ ≤ 1 / 2) :
    ‖∏ p ∈ S, (1 - h p * v p)⁻¹‖ ≤ Real.exp (2 * ∑ p ∈ S, ‖v p‖) ∧
      ‖∏ p ∈ S, (1 - h p * v p)⁻¹‖ ≤ 2 ^ S.card := by
  have hn : ∀ p ∈ S, ‖h p * v p‖ ≤ ‖v p‖ := fun p _ => by
    rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hh p)
  have hf : ∀ p ∈ S,
      ‖(1 - h p * v p)⁻¹‖ ≤ Real.exp (2 * ‖v p‖) ∧ ‖(1 - h p * v p)⁻¹‖ ≤ 2 := fun p hp => by
    obtain ⟨a, b⟩ := norm_inv_one_sub_le_exp ((hn p hp).trans (hv p hp))
    exact ⟨a.trans (Real.exp_le_exp.mpr (by linarith [hn p hp])), b⟩
  rw [norm_prod]
  constructor
  · rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => (hf p hp).1
  · calc ∏ p ∈ S, ‖(1 - h p * v p)⁻¹‖ ≤ ∏ _p ∈ S, (2 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => (hf p hp).2
      _ = 2 ^ S.card := Finset.prod_const _

/-- **Two-level zero planting.** -/
theorem exists_twoLevel_charProduct_zero {N : ℕ} [NeZero N] {C : DirichletCharacter ℂ N → ℂ}
    {χ₁ χ₂ : DirichletCharacter ℂ N} (h12 : χ₁ ≠ χ₂) (h1 : C χ₁ ≠ 0) (h2 : C χ₂ ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ (N' : ℕ) [NeZero N'] (_ : N ∣ N') (P₀ : ℕ)
      (D : DirichletCharacter ℂ N' → ℂ), (∀ ψ, D ψ ≠ 0 → ¬ ψ.FactorsThrough N) →
      ∑ ψ, ‖D ψ‖ ≤ ‖C χ₁‖ / 96 →
      ∀ {ι : Type} (e : ι → ℂ) (g : ι → ℕ → ℂ), Summable (fun j => ‖e j‖) →
        ∑' j, ‖e j‖ ≤ η → (∀ j p, ‖g j p‖ ≤ 1) →
        ∃ σ : ℝ, 1 < σ ∧ ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ IsUnit (p : ZMod N') ∧ P₀ < p) ∧
          ∃ z : ℕ → ℂ, (∀ p ∈ S, ‖z p‖ ≤ ((p : ℝ)) ^ (-σ)) ∧
            ∑ ξ, C ξ * ∏ p ∈ S, (1 - ξ p * z p)⁻¹ +
              ∑ ψ, D ψ * ∏ p ∈ S, (1 - ψ p * z p)⁻¹ +
              ∑' j, e j * ∏ p ∈ S, (1 - g j p * z p)⁻¹ = 0 := by
  obtain ⟨η, hη, H⟩ := exists_twoLevel_zero_of_far h12 h1 h2
  refine ⟨η, hη, fun N' _ hNN P₀ D hD hDsum ι e g he hesum hg => ?_⟩
  have hbound : ∀ (S : Finset ℕ) (v : ℕ → ℂ), (∀ p, p ∉ S → v p = 0) →
      (∀ p ∈ S, ‖v p‖ ≤ 1 / 2) → ‖∑' j, e j * ∏ p ∈ S, (1 - g j p * v p)⁻¹‖ ≤
        η * Real.exp (2 * ∑ p ∈ S, ‖v p‖) := by
    intro S v _ hv
    have hb := fun j => norm_prod_inv_one_sub_le (S := S) (hg j) hv
    have hle : ∀ j, ‖e j * ∏ p ∈ S, (1 - g j p * v p)⁻¹‖ ≤
        ‖e j‖ * Real.exp (2 * ∑ p ∈ S, ‖v p‖) := fun j => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb j).1 (norm_nonneg _)
    have hs : Summable fun j => ‖e j * ∏ p ∈ S, (1 - g j p * v p)⁻¹‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (he.mul_right _)
    refine (norm_tsum_le_tsum_norm hs).trans ?_
    calc ∑' j, ‖e j * ∏ p ∈ S, (1 - g j p * v p)⁻¹‖
        ≤ ∑' j, ‖e j‖ * Real.exp (2 * ∑ p ∈ S, ‖v p‖) := hs.tsum_le_tsum hle (he.mul_right _)
      _ = (∑' j, ‖e j‖) * Real.exp (2 * ∑ p ∈ S, ‖v p‖) := tsum_mul_right
      _ ≤ η * Real.exp (2 * ∑ p ∈ S, ‖v p‖) :=
          mul_le_mul_of_nonneg_right hesum (Real.exp_pos _).le
  have hdiff : ∀ (S : Finset ℕ) (zt : ℂ → ℕ → ℂ) (U : Set ℂ), IsOpen U →
      (∀ p, Differentiable ℂ (fun t => zt t p)) → (∀ t ∈ U, ∀ p, p ∉ S → zt t p = 0) →
      (∀ t ∈ U, ∀ p ∈ S, ‖zt t p‖ ≤ 1 / 2) →
      DifferentiableOn ℂ (fun t => ∑' j, e j * ∏ p ∈ S, (1 - g j p * zt t p)⁻¹) U := by
    intro S zt U hU hd _ hv
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun j => ‖e j‖ * 2 ^ S.card)
      (he.mul_right _) (fun j t ht => ?_) hU (fun j t ht => ?_)
    · have hsm : ∀ p ∈ S, ‖g j p * zt t p‖ ≤ 1 / 2 := fun p hp => by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hg j p)).trans (hv t ht p hp)
      exact ((differentiableAt_const _).mul
        (differentiableAt_prod_inv hd hsm)).differentiableWithinAt
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_prod_inv_one_sub_le (hg j) (hv t ht)).2
        (norm_nonneg _)
  obtain ⟨σ, hσ, S, hS, z, hz, -, h0⟩ := H N' hNN P₀ D hD hDsum
    (fun S v => ∑' j, e j * ∏ p ∈ S, (1 - g j p * v p)⁻¹) hbound hdiff
  exact ⟨σ, hσ, S, hS, z, hz, h0⟩

/-! ## Power-series far parts -/

/-- The completely multiplicative function with prime values `v` vanishes off the `S`-factored
numbers when `v` vanishes off `S`. -/
theorem primeValueTwist_eq_zero_of_not_mem {v : ℕ → ℂ} {S : Finset ℕ}
    (hv : ∀ p, p ∉ S → v p = 0) {n : ℕ} (hn : n ∉ Nat.factoredNumbers S) :
    primeValueTwist v n = 0 := by
  by_cases hn0 : n = 0
  · rw [hn0, map_zero]
  obtain ⟨p, hpl, hpS⟩ : ∃ p ∈ n.primeFactorsList, p ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hn (Nat.mem_factoredNumbers.mpr ⟨hn0, hcon⟩)
  have hp := Nat.prime_of_mem_primeFactorsList hpl
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_primeFactorsList hpl
  rw [map_mul, primeValueTwist_prime v hp, hv p hpS, zero_mul]

/-- Comparison of completely multiplicative functions by their prime values. -/
theorem norm_primeValueTwist_le_of_le {v w : ℕ → ℂ} (h : ∀ p, p.Prime → ‖v p‖ ≤ ‖w p‖) (n : ℕ) :
    ‖primeValueTwist v n‖ ≤ ‖primeValueTwist w n‖ := by
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp
  | prime p hp => rw [primeValueTwist_prime v hp, primeValueTwist_prime w hp]; exact h p hp
  | mul a b ha hb =>
    rw [map_mul, map_mul, norm_mul, norm_mul]
    exact mul_le_mul ha hb (norm_nonneg _) (norm_nonneg _)

/-- **Euler bound.** If `v` vanishes off `S` and `|v_p| ≤ ½` on `S`, then the completely
multiplicative function with prime values `v` is absolutely summable, with
`Σ_n |f(n)| = Π_{p∈S}(1 − |v_p|)^{−1} ≤ e^{2Σ_S|v_p|}`. -/
theorem summable_norm_primeValueTwist {S : Finset ℕ} {v : ℕ → ℂ} (hv0 : ∀ p, p ∉ S → v p = 0)
    (hv : ∀ p ∈ S, ‖v p‖ ≤ 1 / 2) :
    Summable (fun n => ‖primeValueTwist v n‖) ∧
      ∑' n, ‖primeValueTwist v n‖ ≤ Real.exp (2 * ∑ p ∈ S, ‖v p‖) := by
  classical
  set f : ℕ →* ℝ := ((normHom : ℂ →*₀ ℝ).comp (primeValueTwist v)).toMonoidHom with hf
  have hfv : ∀ n, f n = ‖primeValueTwist v n‖ := fun n => rfl
  have hvp : ∀ p, ‖v p‖ ≤ 1 / 2 := fun p => by
    by_cases hp : p ∈ S
    · exact hv p hp
    · rw [hv0 p hp, norm_zero]; norm_num
  have hlt : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1 := fun {p} hp => by
    rw [hfv, norm_norm, primeValueTwist_prime v hp]; linarith [hvp p]
  obtain ⟨hs, hh⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hlt S
  have hsupp : Function.support (fun n => ‖primeValueTwist v n‖) ⊆ Nat.factoredNumbers S := by
    intro n hn
    by_contra hns
    exact hn (show ‖primeValueTwist v n‖ = 0 by
      rw [primeValueTwist_eq_zero_of_not_mem hv0 hns, norm_zero])
  have hs' : Summable fun m : Nat.factoredNumbers S => ‖primeValueTwist v m‖ :=
    hs.congr fun m => by rw [hfv, norm_norm]
  have hsum : Summable fun n => ‖primeValueTwist v n‖ := by
    have := (summable_subtype_iff_indicator (f := fun n => ‖primeValueTwist v n‖)
      (s := Nat.factoredNumbers S)).mp hs'
    rwa [Set.indicator_eq_self.mpr hsupp] at this
  refine ⟨hsum, ?_⟩
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  have hsub : ∑ p ∈ S with p.Prime, ‖v p‖ ≤ ∑ p ∈ S, ‖v p‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S) fun p _ _ => norm_nonneg _
  calc ∑' m : Nat.factoredNumbers S, ‖primeValueTwist v m‖ = ∑' m : Nat.factoredNumbers S, f m :=
        rfl
    _ = ∏ p ∈ S with p.Prime, (1 - f p)⁻¹ := hh.tsum_eq
    _ = ∏ p ∈ S with p.Prime, (1 - ‖v p‖)⁻¹ := Finset.prod_congr rfl fun p hp => by
        rw [hfv, primeValueTwist_prime v (Finset.mem_filter.mp hp).2]
    _ ≤ ∏ p ∈ S with p.Prime, Real.exp (2 * ‖v p‖) :=
        Finset.prod_le_prod (fun p _ => inv_nonneg.mpr (by linarith [hvp p]))
          fun p _ => inv_one_sub_le_exp_two_mul (norm_nonneg _) (hvp p)
    _ = Real.exp (2 * ∑ p ∈ S with p.Prime, ‖v p‖) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ Real.exp (2 * ∑ p ∈ S, ‖v p‖) := Real.exp_le_exp.mpr (by linarith)

/-- Holomorphic prime values give holomorphic completely multiplicative values. -/
theorem differentiable_primeValueTwist {zt : ℂ → ℕ → ℂ}
    (hd : ∀ p, Differentiable ℂ fun t => zt t p) (n : ℕ) :
    Differentiable ℂ fun t => primeValueTwist (zt t) n := by
  induction n using Nat.recOnMul with
  | zero => simp only [map_zero]; exact differentiable_const _
  | one => simp only [map_one]; exact differentiable_const _
  | prime p hp => simp only [primeValueTwist_prime _ hp]; exact hd p
  | mul a b ha hb => simp only [map_mul]; exact ha.mul hb

/-- A power series `Σ_n τ_n f_v(n)` in the prime values `v`, with `|τ_n| ≤ η`, converges
absolutely and is at most `η e^{2Σ_S|v_p|}`. -/
theorem norm_tsum_mul_primeValueTwist_le {S : Finset ℕ} {v τ : ℕ → ℂ} {η : ℝ}
    (hτ : ∀ n, ‖τ n‖ ≤ η) (hv0 : ∀ p, p ∉ S → v p = 0) (hv : ∀ p ∈ S, ‖v p‖ ≤ 1 / 2) :
    Summable (fun n => ‖τ n * primeValueTwist v n‖) ∧
      ‖∑' n, τ n * primeValueTwist v n‖ ≤ η * Real.exp (2 * ∑ p ∈ S, ‖v p‖) := by
  obtain ⟨hs, hle⟩ := summable_norm_primeValueTwist hv0 hv
  have hη : 0 ≤ η := (norm_nonneg _).trans (hτ 0)
  have hb : ∀ n, ‖τ n * primeValueTwist v n‖ ≤ η * ‖primeValueTwist v n‖ := fun n => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hτ n) (norm_nonneg _)
  have hs' : Summable fun n => ‖τ n * primeValueTwist v n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hs.mul_left η)
  refine ⟨hs', (norm_tsum_le_tsum_norm hs').trans ?_⟩
  calc ∑' n, ‖τ n * primeValueTwist v n‖ ≤ ∑' n, η * ‖primeValueTwist v n‖ :=
        hs'.tsum_le_tsum hb (hs.mul_left η)
    _ = η * ∑' n, ‖primeValueTwist v n‖ := tsum_mul_left
    _ ≤ η * Real.exp (2 * ∑ p ∈ S, ‖v p‖) := mul_le_mul_of_nonneg_left hle hη

/-- The power series `t ↦ Σ_n τ_n f_{z(t)}(n)` is holomorphic where the prime values `z(t)` are
holomorphic, supported on `S` and at most `½`. -/
theorem differentiableOn_tsum_mul_primeValueTwist {S : Finset ℕ} {τ : ℕ → ℂ} {η : ℝ}
    (hτ : ∀ n, ‖τ n‖ ≤ η) {zt : ℂ → ℕ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ p, Differentiable ℂ fun t => zt t p) (hz0 : ∀ t ∈ U, ∀ p, p ∉ S → zt t p = 0)
    (hz : ∀ t ∈ U, ∀ p ∈ S, ‖zt t p‖ ≤ 1 / 2) :
    DifferentiableOn ℂ (fun t => ∑' n, τ n * primeValueTwist (zt t) n) U := by
  classical
  set b : ℕ → ℂ := fun p => if p ∈ S then 1 / 2 else 0 with hb
  have hbn : ∀ p ∈ S, ‖b p‖ = 1 / 2 := fun p hp => by
    simp only [hb, if_pos hp]; norm_num
  have hb0 : ∀ p, p ∉ S → b p = 0 := fun p hp => by simp only [hb, if_neg hp]
  have hη : 0 ≤ η := (norm_nonneg _).trans (hτ 0)
  refine Complex.differentiableOn_tsum_of_summable_norm
    ((summable_norm_primeValueTwist hb0 fun p hp => (hbn p hp).le).1.mul_left η)
    (fun n => ((differentiable_const _).mul (differentiable_primeValueTwist hd n)).differentiableOn)
    hU (fun n t ht => ?_)
  rw [norm_mul]
  refine mul_le_mul (hτ n) (norm_primeValueTwist_le_of_le (fun p _ => ?_) n) (norm_nonneg _) hη
  by_cases hp : p ∈ S
  · rw [hbn p hp]; exact hz t ht p hp
  · rw [hz0 t ht p hp, norm_zero]; exact norm_nonneg _

/-- **Two-level zero planting with a power-series far part.** For every far part
`Σ_n τ_n f_z(n)` with `|τ_n| ≤ η`, where `f_z` is the completely multiplicative function with
prime values `z`, the zero is planted with `z` supported on `S`. -/
theorem exists_twoLevel_zero_of_powerSeries {N : ℕ} [NeZero N] {C : DirichletCharacter ℂ N → ℂ}
    {χ₁ χ₂ : DirichletCharacter ℂ N} (h12 : χ₁ ≠ χ₂) (h1 : C χ₁ ≠ 0) (h2 : C χ₂ ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ (N' : ℕ) [NeZero N'] (_ : N ∣ N') (P₀ : ℕ)
      (D : DirichletCharacter ℂ N' → ℂ), (∀ ψ, D ψ ≠ 0 → ¬ ψ.FactorsThrough N) →
      ∑ ψ, ‖D ψ‖ ≤ ‖C χ₁‖ / 96 → ∀ τ : ℕ → ℂ, (∀ n, ‖τ n‖ ≤ η) →
        ∃ σ : ℝ, 1 < σ ∧ ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ IsUnit (p : ZMod N') ∧ P₀ < p) ∧
          ∃ z : ℕ → ℂ, (∀ p ∈ S, ‖z p‖ ≤ ((p : ℝ)) ^ (-σ)) ∧ (∀ p, p ∉ S → z p = 0) ∧
            ∑ ξ, C ξ * ∏ p ∈ S, (1 - ξ p * z p)⁻¹ +
              ∑ ψ, D ψ * ∏ p ∈ S, (1 - ψ p * z p)⁻¹ +
              ∑' n, τ n * primeValueTwist z n = 0 := by
  obtain ⟨η, hη, H⟩ := exists_twoLevel_zero_of_far h12 h1 h2
  refine ⟨η, hη, fun N' _ hNN P₀ D hD hDsum τ hτ => ?_⟩
  exact H N' hNN P₀ D hD hDsum (fun _ v => ∑' n, τ n * primeValueTwist v n)
    (fun _ _ hv0 hv => (norm_tsum_mul_primeValueTwist_le hτ hv0 hv).2)
    (fun _ _ _ hU hd hz0 hz => differentiableOn_tsum_mul_primeValueTwist hτ hU hd hz0 hz)

end

end CharacterZeroPlanting

end RHTower
