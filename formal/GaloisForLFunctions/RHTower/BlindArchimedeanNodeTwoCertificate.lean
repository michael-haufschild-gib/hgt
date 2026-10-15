import GaloisForLFunctions.RHTower.ArchimedeanPoleValueFunction
import GaloisForLFunctions.RHTower.WeilSymbolMertensExpansion
import GaloisForLFunctions.RHTower.OddDirichletSingleNodeConductorThreshold
import GaloisForLFunctions.RHTower.WeilBlindPoleSignLaw

/-!
# A one-prime certificate for the archimedean symbol on the blind cone, and the slack invariants

Write `γ(r) = Re ψ(¼ + ir/2) − log π` for the archimedean symbol (`EF.gammaBracket`), so
`γ(0) = ψ(¼) − log π ≈ −5.37` is the anomaly, and `γ(r) − γ(0) = Σ_{n ≥ 0} y²/((n+¼)((n+¼)² + y²))`
with `y = r/2` (vertical Gauss expansion).

**Pointwise certificate** (`two_mul_one_sub_cos_le_gammaBracket_sub`).  For every real `r`,
`2(1 − cos(r log 2)) ≤ γ(r) − γ(0)`.  Only the two first Gauss terms are used: for `|r| ≤ 2` the
first term `16r²/(1+4r²)` beats `(r log 2)²`, and for `|r| ≥ 2` the two terms together exceed `4`.

**Integrated certificate** (`node_two_certificate_le_weilArchRe`).  For every Weil test `f` with
autocorrelation `k`, `Re P(k) + (γ(0) + 2) ‖f‖² − √2 ℓ₂(f) ≤ weilArchRe k`, where `ℓ₂(f)` is the
normalized value of `k` at `±log 2`.  On combinations blind at the node `2` the last term vanishes
(`sum_node_two_certificate_of_blind_two`): blindness at the single prime `2` improves the anomaly
`γ(0)` of `WeilBlindPoleSignLaw` to `γ(0) + 2 ≈ −3.37`.

**Slack invariants.**  `BlindSymbolSlack M` says that the archimedean symbol integrated against the
spectral measure of a blind nonnegative combination is at least `−M` times its mass;
`ZeroPoleBlindSymbolSlack M` is the same on combinations of total pole mass zero.
* `blindSymbolSlack_node_two`: `BlindSymbolSlack (−γ(0) − 2)` holds unconditionally.
* `not_blindSymbolSlack_of_nonpos`: `BlindSymbolSlack M` fails for every `M ≤ 0` (pole-weight
  rigidity produces a blind combination with negative symbol integral).  So the symbol alone has a
  definite negative part on the blind cone, of size between `0` and `−γ(0) − 2`.
* `riemannHypothesis_iff_forall_pos_zeroPoleBlindSymbolSlack`: RH holds iff
  `ZeroPoleBlindSymbolSlack M` holds for every `M > 0`.  The pole constraint must remove the whole
  negative part that the symbol alone retains.
-/

open Complex MeasureTheory Set Finsupp Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-! ## The pointwise certificate -/

/-- The first two Gauss terms of the vertical digamma expansion at `a = 1/4`, in `y = r/2`. -/
theorem gauss_two_terms_le_gammaBracket_sub (r : ℝ) :
    (r / 2) ^ 2 / ((1 / 4) * ((1 / 4) ^ 2 + (r / 2) ^ 2)) +
      (r / 2) ^ 2 / ((1 / 4 + 1) * ((1 / 4 + 1) ^ 2 + (r / 2) ^ 2)) ≤
      EF.gammaBracket r - EF.gammaBracket 0 := by
  have h := hasSum_re_digamma_vertical_sub (a := (1 / 4 : ℝ)) (by norm_num) (r / 2)
  have hsum := sum_le_hasSum (Finset.range 2) (fun n _ => by positivity) h
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum
  simp only [Nat.cast_zero, add_zero, Nat.cast_one] at hsum
  have e1 : (1 / 4 : ℂ) + I * (r : ℂ) / 2 = ((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have e0 : (1 / 4 : ℂ) + I * ((0 : ℝ) : ℂ) / 2 = ((1 / 4 : ℝ) : ℂ) := by push_cast; ring
  unfold EF.gammaBracket
  rw [e1, e0]
  linarith

/-- **The one-prime certificate**: `2(1 − cos(r log 2)) ≤ γ(r) − γ(0)` for every real `r`. -/
theorem two_mul_one_sub_cos_le_gammaBracket_sub (r : ℝ) :
    2 * (1 - Real.cos (r * Real.log 2)) ≤ EF.gammaBracket r - EF.gammaBracket 0 := by
  refine le_trans ?_ (gauss_two_terms_le_gammaBracket_sub r)
  have hT0 : (r / 2) ^ 2 / ((1 / 4) * ((1 / 4) ^ 2 + (r / 2) ^ 2)) =
      16 * r ^ 2 / (1 + 4 * r ^ 2) := by
    field_simp
    ring
  have hT1 : (r / 2) ^ 2 / ((1 / 4 + 1) * ((1 / 4 + 1) ^ 2 + (r / 2) ^ 2)) =
      16 * r ^ 2 / (5 * (25 + 4 * r ^ 2)) := by
    field_simp
    ring
  rw [hT0, hT1]
  have hl2 : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
  have hl2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hr0 : 0 ≤ r ^ 2 := sq_nonneg r
  rcases le_or_gt (r ^ 2) 4 with hr | hr
  · have hcos := Real.one_sub_sq_div_two_le_cos (x := r * Real.log 2)
    have h1 : 2 * (1 - Real.cos (r * Real.log 2)) ≤ (r * Real.log 2) ^ 2 := by linarith
    have hlog : (Real.log 2) ^ 2 ≤ 0.49 := by nlinarith
    have h2 : (r * Real.log 2) ^ 2 ≤ 0.49 * r ^ 2 := by
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right hlog hr0
    have h3 : 0.49 * r ^ 2 ≤ 16 * r ^ 2 / (1 + 4 * r ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr)]
    have h4 : 0 ≤ 16 * r ^ 2 / (5 * (25 + 4 * r ^ 2)) := by positivity
    linarith
  · have h1 : 2 * (1 - Real.cos (r * Real.log 2)) ≤ 4 := by
      linarith [Real.neg_one_le_cos (r * Real.log 2)]
    have h3 : (64 : ℝ) / 17 ≤ 16 * r ^ 2 / (1 + 4 * r ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    have h4 : (64 : ℝ) / 205 ≤ 16 * r ^ 2 / (5 * (25 + 4 * r ^ 2)) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    have : (4 : ℝ) ≤ 64 / 17 + 64 / 205 := by norm_num
    linarith

/-! ## The integrated certificate -/

/-- **The node-two certificate for a single test**:
`Re P(k) + (γ(0) + 2) ‖f‖² − √2 ℓ₂(f) ≤ weilArchRe k`. -/
theorem node_two_certificate_le_weilArchRe (f : WeilTestFn) :
    (weilPoleTerm (EF.weilTest f.1 f.1)).re + (EF.gammaBracket 0 + 2) * (∫ x, ‖f.1 x‖ ^ 2) -
        Real.sqrt 2 * logValue f.1 2 ≤
      weilArchRe (EF.weilTest f.1 f.1) := by
  obtain ⟨F, hF, hFc⟩ := f
  simp only
  have hFcont := hF.continuous
  obtain ⟨a, ha⟩ := hFc.isCompact.isBounded.subset_closedBall 0
  have hsupp : tsupport F ⊆ Icc (-a) a := by
    intro x hx
    have := ha hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.mp this
  have hplanch := integral_norm_paperFT_sq hF hsupp
  have hcos := integral_normSq_paperFT_mul_cos_eq hF hsupp (Real.log 2)
  have hintcos := integrable_normSq_paperFT_mul_cos hF hsupp (Real.log 2)
  have hsq : Integrable fun τ : ℝ => ‖paperFT F τ‖ ^ 2 := by
    have := integrable_normSq_paperFT_mul_cos hF hsupp 0
    simpa using this
  -- the archimedean integrand
  have hint := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hF hFc hF hFc
  have hreal : ∀ r : ℝ, paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
    rw [paperFT_weilTest_self_ofReal hFcont hFc r]
    push_cast
    ring
  have hintR : Integrable fun r : ℝ => ‖paperFT F r‖ ^ 2 * EF.gammaBracket r :=
    hint.re.congr (Filter.Eventually.of_forall fun r => by
      simp only
      rw [hreal r]
      exact Complex.ofReal_re _)
  have hint_eq : ∫ r : ℝ, paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ) =
      ((∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    simp_rw [hreal]
    exact integral_complex_ofReal
  have hW : weilArchRe (EF.weilTest F F) = (weilPoleTerm (EF.weilTest F F)).re +
      (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r := by
    unfold weilArchRe weilPoleTerm
    rw [hint_eq, Complex.add_re]
    congr 1
    have hc : (1 / (2 * (Real.pi : ℂ))) *
        ((∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) =
        (((1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
      push_cast; ring
    rw [hc, Complex.ofReal_re]
  -- the pointwise certificate integrated against `|F̂|²`
  have hlower : (EF.gammaBracket 0 + 2) * (∫ r : ℝ, ‖paperFT F r‖ ^ 2) -
      2 * ∫ r : ℝ, ‖paperFT F r‖ ^ 2 * Real.cos (r * Real.log 2) ≤
      ∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hsq.const_mul _) (hintcos.const_mul _)]
    refine integral_mono ((hsq.const_mul _).sub (hintcos.const_mul _)) hintR fun r => ?_
    simp only
    have h0 : 0 ≤ ‖paperFT F r‖ ^ 2 := by positivity
    have := two_mul_one_sub_cos_le_gammaBracket_sub r
    nlinarith
  rw [hW]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hℓ : Real.sqrt 2 * logValue F 2 = (EF.weilTest F F (Real.log 2) + EF.weilTest F F (-Real.log 2)).re := by
    unfold logValue
    have h2 : (0 : ℝ) < Real.sqrt (2 : ℕ) := Real.sqrt_pos.mpr (by norm_num)
    push_cast
    field_simp
  have key : (EF.gammaBracket 0 + 2) * (∫ x, ‖F x‖ ^ 2) - Real.sqrt 2 * logValue F 2 ≤
      (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r := by
    rw [hplanch, hcos, ← hℓ] at hlower
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpi]
    nlinarith [Real.pi_pos]
  linarith

/-! ## Sums over nonnegative combinations -/

/-- The mass `Σ c_f ‖f‖²` of a combination. -/
def massOf (c : WeilTestFn →₀ ℝ) : ℝ := c.sum fun f t => t * ∫ x, ‖f.1 x‖ ^ 2

theorem massOf_nonneg {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) : 0 ≤ massOf c :=
  Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (integral_nonneg fun _ => by positivity)

theorem nodePoleMass_eq_sum (c : WeilTestFn →₀ ℝ) :
    nodePoleMass c = c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re := by
  rw [nodePoleMass, linearCombination_apply]
  simp only [smul_eq_mul]

/-- **The node-two certificate summed over a combination.** -/
theorem sum_node_two_certificate (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f) :
    nodePoleMass c + (EF.gammaBracket 0 + 2) * massOf c - Real.sqrt 2 * nodeVector c ⟨2, le_rfl⟩ ≤
      nodeArchEnergy c := by
  rw [nodePoleMass_eq_sum, massOf, nodeVector_eq, linearCombination_logVector_apply,
    nodeArchEnergy_eq, linearCombination_apply]
  simp only [smul_eq_mul]
  rw [Finsupp.mul_sum, Finsupp.mul_sum, ← Finsupp.sum_add, ← Finsupp.sum_sub]
  refine Finsupp.sum_le_sum fun f _ => ?_
  have h := node_two_certificate_le_weilArchRe f
  have := hc f
  nlinarith

/-- **Blindness at the prime `2` improves the anomaly by `2`.**  For a nonnegative combination
blind at `±log 2`, `P(c) + (γ(0) + 2) mass(c) ≤ A(c)`. -/
theorem sum_node_two_certificate_of_blind_two (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f)
    (h2 : nodeVector c ⟨2, le_rfl⟩ = 0) :
    nodePoleMass c + (EF.gammaBracket 0 + 2) * massOf c ≤ nodeArchEnergy c := by
  have := sum_node_two_certificate c hc
  rw [h2, mul_zero, sub_zero] at this
  exact this

/-! ## The slack invariants -/

/-- **Blind symbol slack `M`**: on every nonnegative blind combination the archimedean symbol
integrated against the spectral measure is at least `−M` times the mass. -/
def BlindSymbolSlack (M : ℝ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → nodeVector c = 0 → 0 ≤ nodeArchOnly c + M * massOf c

/-- **Zero-pole blind symbol slack `M`**: the same on the combinations of total pole mass zero. -/
def ZeroPoleBlindSymbolSlack (M : ℝ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → nodeVector c = 0 → nodePoleMass c = 0 →
    0 ≤ nodeArchEnergy c + M * massOf c

theorem BlindSymbolSlack.mono {M M' : ℝ} (hMM' : M ≤ M') (h : BlindSymbolSlack M) :
    BlindSymbolSlack M' := fun c hc hv => by
  have := h c hc hv
  have := massOf_nonneg hc
  nlinarith

theorem ZeroPoleBlindSymbolSlack.mono {M M' : ℝ} (hMM' : M ≤ M') (h : ZeroPoleBlindSymbolSlack M) :
    ZeroPoleBlindSymbolSlack M' := fun c hc hv hp => by
  have := h c hc hv hp
  have := massOf_nonneg hc
  nlinarith

theorem ZeroPoleBlindSymbolSlack.of_blind {M : ℝ} (h : BlindSymbolSlack M) :
    ZeroPoleBlindSymbolSlack M := fun c hc hv hp => by
  have := h c hc hv
  rwa [nodeArchOnly, hp, sub_zero] at this

/-- **The one-prime certificate as a slack bound**: `BlindSymbolSlack (−γ(0) − 2)` holds
unconditionally, with `−γ(0) − 2 ≈ 3.37`. -/
theorem blindSymbolSlack_node_two : BlindSymbolSlack (-EF.gammaBracket 0 - 2) := by
  intro c hc hv
  have h2 : nodeVector c ⟨2, le_rfl⟩ = 0 := by rw [hv]; rfl
  have := sum_node_two_certificate_of_blind_two c hc h2
  rw [nodeArchOnly]
  linarith

/-- **The symbol alone is negative somewhere on the blind cone**: `BlindSymbolSlack M` fails for
every `M ≤ 0`. -/
theorem not_blindSymbolSlack_of_nonpos {M : ℝ} (hM : M ≤ 0) : ¬ BlindSymbolSlack M := by
  intro h
  obtain ⟨c, hc, hnull, hneg⟩ := RHTower.exists_blind_arch_add_mul_pole_neg (ε := -1) (by norm_num)
  have hv : nodeVector c = 0 := linearCombination_logVector_eq_zero hnull
  have h1 := h c hc hv
  have hmass := massOf_nonneg hc
  rw [sum_weilArchRe_eq, ← nodeArchEnergy_eq, ← nodePoleMass_eq_sum] at hneg
  have : nodeArchOnly c < 0 := by rw [nodeArchOnly]; linarith
  nlinarith

/-- **RH is zero-pole blind symbol slack at every positive level.** -/
theorem riemannHypothesis_iff_forall_pos_zeroPoleBlindSymbolSlack :
    RiemannHypothesis ↔ ∀ M : ℝ, 0 < M → ZeroPoleBlindSymbolSlack M := by
  constructor
  · intro hRH M hM c hc hv hp
    have := riemannHypothesis_iff_zeroPoleBlindPositive.mp hRH c hc hv hp
    have := massOf_nonneg hc
    nlinarith
  · intro h
    refine riemannHypothesis_iff_zeroPoleBlindPositive.mpr fun c hc hv hp => ?_
    by_contra hneg
    rw [not_le] at hneg
    have hmass := massOf_nonneg hc
    rcases eq_or_lt_of_le hmass with hm0 | hm0
    · have := h 1 one_pos c hc hv hp
      rw [← hm0, mul_zero, add_zero] at this
      linarith
    · have hpos : 0 < -nodeArchEnergy c / (2 * massOf c) := div_pos (by linarith) (by positivity)
      have := h _ hpos c hc hv hp
      have e : -nodeArchEnergy c / (2 * massOf c) * massOf c = -nodeArchEnergy c / 2 := by
        field_simp
      rw [e] at this
      linarith

end

end RHTower.WeilOneSided

namespace RHTower.WeilOneSided

noncomputable section

/-- **Pole-heavy blind combinations are positive, with the one-prime threshold.**  If a nonnegative
combination is blind at `2` and its pole mass is at least `(−γ(0) − 2)` times its mass, its pole and
archimedean energy is nonnegative.  This lowers the threshold `−γ(0) ≈ 5.37` of
`sum_weilArchRe_nonneg_of_pole_ge` to `−γ(0) − 2 ≈ 3.37`. -/
theorem nodeArchEnergy_nonneg_of_blind_two_of_pole_ge (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f)
    (h2 : nodeVector c ⟨2, le_rfl⟩ = 0)
    (hP : (-EF.gammaBracket 0 - 2) * massOf c ≤ nodePoleMass c) : 0 ≤ nodeArchEnergy c := by
  have := sum_node_two_certificate_of_blind_two c hc h2
  linarith

/-- **Violators are pole-light.**  A blind combination with negative pole and archimedean energy
has pole mass below `(−γ(0) − 2)` times its mass. -/
theorem nodePoleMass_lt_of_nodeArchEnergy_neg (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f)
    (h2 : nodeVector c ⟨2, le_rfl⟩ = 0) (hA : nodeArchEnergy c < 0) :
    nodePoleMass c < (-EF.gammaBracket 0 - 2) * massOf c := by
  have := sum_node_two_certificate_of_blind_two c hc h2
  linarith

end

end RHTower.WeilOneSided
