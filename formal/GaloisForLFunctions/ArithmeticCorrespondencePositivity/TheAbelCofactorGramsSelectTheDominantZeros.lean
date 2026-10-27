import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelEscapeCapacityOfTheDominantZeros
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheCofactorGramIsATranslationGram

/-!
# The Abel cofactor Grams select the dominant zeros

The escape states of ADR and ACG are limits of the normalized cofactor Grams
`⟨D_j v, D_k v⟩_T / ‖v‖_T²` in the pronic pairing `Σ_{n ≤ T} f(n) h(n)/(n(n+1))`. Replacing the sharp
horizon by an Abel weight gives the **Abel cofactor pairing**
`⟨f, h⟩_c = Σ_m f(m) h(m) w_c(m)`, `w_c(m) = (m^{−(2c+1)} − (m+1)^{−(2c+1)})/(2c+1)`,
with `w_0(m) = 1/(m(m+1))` the pronic weight (`abelWeight_zero`).

* **The Abel cofactor pairing is the Abel Gram of the log profile**
  (`abelGram_logProfile_eq_abelPairing`). For `v(0) = 0` and `e^{−cu} g_v ∈ L²`,
  `A_c(log j, log k) = √j √k ⟨D_j v, D_k v⟩_c`: on each log cell both dilates are constant and the
  Abel weight is `∫_{cell} e^{−(2c+1)u}`.
* **The Abel completeness criterion for `ζ`** (`tendsto_receiver_abelPairing_div`). Let the
  damped Möbius receiver be dominated at `θ` by finitely many simple zeros `ρ` on
  `Re ρ = θ + ½ + ε`, and let the spectral mass of its symbol outside their windows be `o(1/e)`.
  Then the normalized Abel cofactor Grams converge to the diagonal kernel of those zeros:
  `⟨D_j A, D_k A⟩_{θ+e} / ⟨A, A⟩_{θ+e} → (jk)^{−θ−½} Σ_ρ ‖r_ρ‖² cos(Im ρ · log(j/k)) / Σ_ρ ‖r_ρ‖²`.

This is the Abel form of `TheEscapeCompletenessCriterion` (P27): the time-domain split of the row
is replaced by a condition on the symbol, the vanishing of the mass at infinite height, which
`TheAbelEscapeCapacityOfTheDominantZeros` shows to fail exactly in the degenerate cases.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.ArithmeticDefectRigidity (logProfile mem_Ico_log_iff)
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy (rowDilate dampedMobiusEnergy)

/-- The Abel weight `w_c(m) = (m^{−(2c+1)} − (m+1)^{−(2c+1)})/(2c+1)`. -/
def abelWeight (c : ℝ) (m : ℕ) : ℝ :=
  (((m : ℝ)) ^ (-(2 * c + 1)) - ((m : ℝ) + 1) ^ (-(2 * c + 1))) / (2 * c + 1)

/-- At `c = 0` the Abel weight is the pronic weight `1/(m(m+1))`. -/
theorem abelWeight_zero {m : ℕ} (hm : 1 ≤ m) :
    abelWeight 0 m = 1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [abelWeight, mul_zero, zero_add, Real.rpow_neg_one, div_one]
  field_simp
  ring

/-- The Abel cofactor pairing `⟨f, h⟩_c = Σ_m f(m) h(m) w_c(m)`. -/
def abelPairing (c : ℝ) (f h : ℕ → ℝ) : ℝ := ∑' m : ℕ, f m * h m * abelWeight c m

/-- `∫_{log(n+1)}^{log(n+2)} e^{−bu} du = ((n+1)^{−b} − (n+2)^{−b})/b`. -/
theorem integral_logCell_exp {b : ℝ} (hb : b ≠ 0) (n : ℕ) :
    ∫ u in logCell n, Real.exp (-(b * u)) =
      (((n : ℝ) + 1) ^ (-b) - ((n : ℝ) + 2) ^ (-b)) / b := by
  rw [logCell, integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (log_succ_le n)]
  have hderiv : ∀ x ∈ uIcc (Real.log ((n : ℝ) + 1)) (Real.log ((n : ℝ) + 2)),
      HasDerivAt (fun u : ℝ => -1 / b * Real.exp ((-b) * u)) (Real.exp (-(b * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => (-b) * u) (-b) x := by
      simpa using (hasDerivAt_id x).const_mul (-b)
    refine (h1.exp.const_mul (-1 / b)).congr_deriv ?_
    rw [neg_mul b x]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(b * u))).intervalIntegrable _ _)]
  have e : ∀ x : ℝ, 0 < x → Real.exp ((-b) * Real.log x) = x ^ (-b) := fun x hx => by
    rw [Real.rpow_def_of_pos hx]; ring_nf
  rw [e _ (by positivity), e _ (by positivity)]
  field_simp
  ring

/-- The log profile vanishes on the negative half-line when `v(0) = 0`. -/
theorem logProfile_of_neg {v : ℕ → ℝ} (hv0 : v 0 = 0) {u : ℝ} (hu : u < 0) :
    logProfile v u = 0 := by
  rw [logProfile, floor_exp_eq_zero_of_neg hu, hv0, mul_zero]

/-- The integrand `e^{−2cu} g_v(u − log j) g_v(u − log k)` of the Abel Gram at dilations. -/
def abelIntegrand (v : ℕ → ℝ) (c : ℝ) (j k : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-(2 * c * u)) * (logProfile v (u - Real.log j) * logProfile v (u - Real.log k))

theorem abelGram_logProfile_eq_integral (v : ℕ → ℝ) (c : ℝ) (j k : ℕ) :
    abelGram (logProfile v) c (Real.log j) (Real.log k) = ∫ u, abelIntegrand v c j k u := rfl

/-- The Abel integrand is integrable when `e^{−cu} g_v ∈ L²` (two translates of an `L²` function). -/
theorem integrable_abelIntegrand {v : ℕ → ℝ} {c : ℝ}
    (h2 : MemLp (dampedProfile (logProfile v) c) 2) (j k : ℕ) :
    Integrable (abelIntegrand v c j k) := by
  have ha : MemLp (fun u => dampedProfile (logProfile v) c (u - Real.log j)) 2 :=
    h2.comp_measurePreserving (measurePreserving_sub_right _ _)
  have hb : MemLp (fun u => dampedProfile (logProfile v) c (u - Real.log k)) 2 :=
    h2.comp_measurePreserving (measurePreserving_sub_right _ _)
  refine ((ha.integrable_mul hb).const_mul
    (Real.exp (-(c * (Real.log j + Real.log k))))).congr (Eventually.of_forall fun u => ?_)
  simp only [abelIntegrand, Pi.mul_apply, dampedProfile]
  have : Real.exp (-(2 * c * u)) = Real.exp (-(c * (Real.log j + Real.log k))) *
      (Real.exp (-(c * (u - Real.log j))) * Real.exp (-(c * (u - Real.log k)))) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [this]; ring

/-- The Abel integrand vanishes on the negative half-line. -/
theorem abelIntegrand_of_neg {v : ℕ → ℝ} (hv0 : v 0 = 0) (c : ℝ) {j k : ℕ} (hj : 1 ≤ j) {u : ℝ}
    (hu : u < 0) : abelIntegrand v c j k u = 0 := by
  have hj0 : (0 : ℝ) ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj)
  rw [abelIntegrand, logProfile_of_neg hv0 (show u - Real.log j < 0 by linarith), zero_mul,
    mul_zero]

/-- On the log cell `⌊e^u⌋ = n + 1` the Abel integrand integrates to
`√j √k v((n+1)/j) v((n+1)/k) w_c(n+1)`. -/
theorem integral_logCell_abelIntegrand (v : ℕ → ℝ) {c : ℝ} (hc : 2 * c + 1 ≠ 0) {j k : ℕ}
    (hj : 1 ≤ j) (hk : 1 ≤ k) (n : ℕ) :
    ∫ u in logCell n, abelIntegrand v c j k u = Real.sqrt j * Real.sqrt k *
      (rowDilate j v (n + 1) * rowDilate k v (n + 1) * abelWeight c (n + 1)) := by
  have heq : EqOn (abelIntegrand v c j k) (fun u => Real.sqrt j * Real.sqrt k *
      (v ((n + 1) / j) * v ((n + 1) / k)) * Real.exp (-((2 * c + 1) * u))) (logCell n) := by
    intro u hu
    simp only [abelIntegrand]
    rw [translationGram_integrand v hj hk ((mem_Ico_log_iff n).mp hu),
      show -((2 * c + 1) * u) = -(2 * c * u) + -u by ring, Real.exp_add]
    ring
  rw [setIntegral_congr_fun (measurableSet_logCell n) heq, integral_const_mul,
    integral_logCell_exp hc n, abelWeight, rowDilate, rowDilate]
  push_cast
  ring_nf

/-- **The Abel cofactor pairing is the Abel Gram of the log profile.** For `v(0) = 0`, `j, k ≥ 1`,
`2c + 1 ≠ 0` and `e^{−cu} g_v ∈ L²`, `A_c(log j, log k) = √j √k ⟨D_j v, D_k v⟩_c`. -/
theorem abelGram_logProfile_eq_abelPairing {v : ℕ → ℝ} (hv0 : v 0 = 0) {j k : ℕ} (hj : 1 ≤ j)
    (hk : 1 ≤ k) {c : ℝ} (hc : 2 * c + 1 ≠ 0) (h2 : MemLp (dampedProfile (logProfile v) c) 2) :
    abelGram (logProfile v) c (Real.log j) (Real.log k) =
      Real.sqrt j * Real.sqrt k * abelPairing c (rowDilate j v) (rowDilate k v) := by
  have hint := integrable_abelIntegrand h2 j k
  have hsum := hasSum_integral_iUnion measurableSet_logCell pairwise_disjoint_logCell
    (f := abelIntegrand v c j k) (by rw [iUnion_logCell]; exact hint.integrableOn)
  rw [iUnion_logCell] at hsum
  simp_rw [integral_logCell_abelIntegrand v hc hj hk] at hsum
  -- shift to all `m`, the `m = 0` term being zero
  have hsum' := (hasSum_nat_add_iff (f := fun m =>
    Real.sqrt j * Real.sqrt k * (rowDilate j v m * rowDilate k v m * abelWeight c m)) 1).mp hsum
  simp only [Finset.range_one, Finset.sum_singleton, rowDilate, Nat.zero_div, hv0,
    zero_mul, mul_zero, add_zero] at hsum'
  have hjk : Real.sqrt j * Real.sqrt k ≠ 0 := by
    have : (0 : ℝ) < j := by exact_mod_cast hj
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hfin := (hsum'.div_const (Real.sqrt j * Real.sqrt k))
  simp only [mul_div_cancel_left₀ _ hjk] at hfin
  have hIci : ∫ u, abelIntegrand v c j k u = ∫ u in Ici (0 : ℝ), abelIntegrand v c j k u := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ici (0 : ℝ)) fun u hu => ?_).symm
    rw [mem_Ici, not_le] at hu
    exact abelIntegrand_of_neg hv0 c hj hu
  have hpair : abelPairing c (rowDilate j v) (rowDilate k v) =
      (∫ u in Ici (0 : ℝ), abelIntegrand v c j k u) / (Real.sqrt j * Real.sqrt k) :=
    hfin.tsum_eq
  rw [abelGram_logProfile_eq_integral, hIci, hpair, mul_div_cancel₀ _ hjk]

/-- The receiver's log profile is the log profile of the receiver row. -/
theorem receiverLogProfile_eq (ε : ℝ) : receiverLogProfile ε = logProfile (receiver ε) := rfl

/-- **The Abel completeness criterion for `ζ`.** Let the damped Möbius receiver at damping `ε` be
dominant at `θ` (energy `O((T+1)^κ)` for every `κ > 2θ`) with a finite set `s` of simple zeros on
`Re ρ = θ + ½ + ε`, not all cancelled, and let the spectral mass of its symbol outside the windows
of `s` be `o(1/e)` (no mass at infinite height). Then the normalized Abel cofactor Grams converge to
the diagonal kernel of `s` in ADR's normalization:
`⟨D_j A, D_k A⟩_{θ+e}/⟨A, A⟩_{θ+e} → e^{−θ(log j + log k)}/(√j √k) ·
  Σ_ρ ‖r_ρ‖² cos(Im ρ (log j − log k)) / Σ_ρ ‖r_ρ‖²`. -/
theorem tendsto_receiver_abelPairing_div {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ1 : θ + 1 / 2 + ε < 1)
    (hdom : ∀ κ : ℝ, 2 * θ < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ)
    (s : Finset ℂ) (hs : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧
      ρ.re = θ + 1 / 2 + ε)
    (hr : 0 < ∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2)
    (hout : ∀ δ > 0, Tendsto (fun e : ℝ => e * ∫ y in (⋃ ρ ∈ s, Icc (ρ.im - δ) (ρ.im + δ))ᶜ,
      ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) (𝓝[>] 0) (𝓝 0))
    {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    Tendsto (fun e : ℝ => abelPairing (θ + e) (rowDilate j (receiver ε)) (rowDilate k (receiver ε)) /
        abelPairing (θ + e) (receiver ε) (receiver ε)) (𝓝[>] 0)
      (𝓝 (Real.exp (-(θ * (Real.log j + Real.log k))) / (Real.sqrt j * Real.sqrt k) *
        ((∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2 * Real.cos (ρ.im * (Real.log j - Real.log k))) /
          ∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2))) := by
  -- the window pole bounds of the zeros of `s`
  have hwin : ∀ ρ ∈ s, ∃ δ₀ > 0, ∃ M : ℝ, ∀ e ∈ Ioo (0 : ℝ) δ₀, ∀ y ∈ Icc (ρ.im - δ₀) (ρ.im + δ₀),
      ‖lineSymbol (receiverLogProfile ε) (θ + e) y -
        receiverResidue ε ρ / ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)‖ ≤ M := by
    intro ρ hρ
    obtain ⟨hz, hd, hre⟩ := hs ρ hρ
    obtain ⟨δ₀, hδ₀, M, h⟩ := exists_receiver_window_pole_bound hε hz hd (by rw [hre]; linarith)
      (by rw [hre]; linarith) fun κ hκ => hdom κ (by rw [hre] at hκ; linarith)
    refine ⟨δ₀, hδ₀, M, fun e he y hy => ?_⟩
    have := (h e he).2.2 y hy
    rwa [show ρ.re - ε - 1 / 2 = θ by rw [hre]; ring] at this
  choose! δ₀ hδ₀ Mρ hMρ using hwin
  -- a common radius, below every `δ₀` and half of every gap of ordinates
  have hevδ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ (∀ ρ ∈ s, δ ≤ δ₀ ρ) ∧
      ∀ ρ ∈ s, ∀ ρ' ∈ s, ρ ≠ ρ' → 2 * δ < |ρ.im - ρ'.im| := by
    refine eventually_mem_nhdsWithin.and (Filter.Eventually.and ?_ ?_)
    · refine (eventually_all_finset s).mpr fun ρ hρ => ?_
      exact ((gt_mem_nhds (hδ₀ ρ hρ)).filter_mono nhdsWithin_le_nhds).mono fun δ h => h.le
    · refine (eventually_all_finset s).mpr fun ρ hρ => (eventually_all_finset s).mpr fun ρ' hρ' => ?_
      by_cases hne : ρ = ρ'
      · exact Eventually.of_forall fun δ h => absurd hne h
      · have him : ρ.im ≠ ρ'.im := fun h => hne (Complex.ext (by
          rw [(hs ρ hρ).2.2, (hs ρ' hρ').2.2]) h)
        have hpos : 0 < |ρ.im - ρ'.im| := abs_pos.mpr (sub_ne_zero.mpr him)
        exact ((gt_mem_nhds (show (0 : ℝ) < |ρ.im - ρ'.im| / 2 by linarith)).filter_mono
          nhdsWithin_le_nhds).mono fun δ h _ => by linarith
  obtain ⟨δ, hδ0, hδle, hgap⟩ := hevδ.exists
  have hdisj : (s : Set ℂ).Pairwise
      (Function.onFun Disjoint fun ρ : ℂ => Icc (ρ.im - δ) (ρ.im + δ)) := by
    intro ρ hρ ρ' hρ' hne
    refine Set.disjoint_left.mpr fun y hy hy' => ?_
    have hlt := hgap ρ hρ ρ' hρ' hne
    have hle : |ρ.im - ρ'.im| ≤ 2 * δ :=
      abs_le.mpr ⟨by linarith [hy.1, hy.2, hy'.1, hy'.2], by linarith [hy.1, hy.2, hy'.1, hy'.2]⟩
    linarith
  -- the Abel escape law for the receiver
  have hlaw := tendsto_abelGram_div_of_poles (g := receiverLogProfile ε) (θ := θ) (δ := δ)
    (M := ∑ ρ ∈ s, |Mρ ρ|) s (fun ρ => ρ.im) (receiverResidue ε) hδ0
    (Finset.sum_nonneg fun ρ _ => abs_nonneg _) (fun e he => (receiver_data hθ he.1 hdom).1)
    (fun e he => (receiver_data hθ he.1 hdom).2) hdisj
    (fun ρ hρ e he y hy => (hMρ ρ hρ e ⟨he.1, he.2.trans_le (hδle ρ hρ)⟩ y
      ⟨by linarith [hy.1, hδle ρ hρ], by linarith [hy.2, hδle ρ hρ]⟩).trans
      ((le_abs_self _).trans (Finset.single_le_sum (f := fun ρ => |Mρ ρ|)
        (fun ρ _ => abs_nonneg _) hρ)))
    (hout δ hδ0) hr (Real.log j) (Real.log k)
  have hjk : (0 : ℝ) < Real.sqrt j * Real.sqrt k := by
    have : (0 : ℝ) < j := by exact_mod_cast hj
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hlim := hlaw.div_const (Real.sqrt j * Real.sqrt k)
  rw [show Real.exp (-(θ * (Real.log j + Real.log k))) *
      (∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2 * Real.cos (ρ.im * (Real.log j - Real.log k))) /
        (∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2) / (Real.sqrt j * Real.sqrt k) =
      Real.exp (-(θ * (Real.log j + Real.log k))) / (Real.sqrt j * Real.sqrt k) *
        ((∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2 * Real.cos (ρ.im * (Real.log j - Real.log k))) /
          ∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2) by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  have he0 : (0 : ℝ) < e := he
  have hL := (receiver_data hθ he0 hdom).2
  have hc : 2 * (θ + e) + 1 ≠ 0 := by linarith
  have hjk' := abelGram_logProfile_eq_abelPairing (v := receiver ε)
    (TransHorizonIncidenceMechanics.weightCenteredPrefix_zero _ _) hj hk hc hL
  have h11 := abelGram_logProfile_eq_abelPairing (v := receiver ε)
    (TransHorizonIncidenceMechanics.weightCenteredPrefix_zero _ _) le_rfl le_rfl hc hL
  simp only [Nat.cast_one, Real.log_one, Real.sqrt_one, one_mul] at h11
  have hrow : rowDilate 1 (receiver ε) = receiver ε := by
    funext n; simp [rowDilate]
  rw [hrow] at h11
  rw [← receiverLogProfile_eq] at hjk' h11
  rw [hjk', h11]
  field_simp

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
