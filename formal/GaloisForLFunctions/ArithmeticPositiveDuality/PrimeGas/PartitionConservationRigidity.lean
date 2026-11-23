import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.MissingDirection
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.RankCorrection
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.QuantumCriterion
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.IntrinsicDirichletCutoffMargin

/-!
# Commutant rigidity, sharp `ζ(2)` fourth-trace stability, and one-sided partition conservation above `84.5`

Approximate matching of the fourth trace `opTrace (G^4) ≈ ζ(2)` fails to isolate `criticalOperator`
among positive conserving propagators because rank-one packet omissions approach `ζ(2)` arbitrarily
closely while keeping a nonzero missing subspace (`MissingDirection`, `CriticalDeficit`). Here we
resolve the exact metric and symmetry laws governing that boundary and connect them directly to the
partition-vanishing conservation criterion above Bohman height `169 / 2 = 84.5`:

1. **Trace-free commutant and shell-diagonal rigidity (`commuting_positive_conserving_iff_eq_critical`,
   `noncanonical_positive_conserving_breaks_shell_diagonal`)**: among positive conserving operators
   `G`, commuting with `criticalOperator` (`G * criticalOperator = criticalOperator * G`, or even
   `G^2 * criticalOperator = criticalOperator * G^2`) forces `G = criticalOperator` with **zero trace
   measurement**. Contrapositively, **every** noncanonical positive conserving operator (of arbitrary
   missing codimension) mixes distinct occupation shells.
2. **Sharp constant-`1` operator/HS stability vs. unit range-defect gap
   (`hsNormSq_critical_sq_sub_sq_le_fourth_trace_defect`,
   `norm_critical_sq_sub_sq_le_sqrt_fourth_trace_defect`,
   `norm_omitted_eq_one_of_ne_critical`, `tendsto_tiltedShell_stability_ratio_one`)**: for every
   positive conserving `G = projected P`, the fourth-trace deficit
   `Δ(G) = (riemannZeta 2).re - (opTrace (G^4)).re` bounds the squared propagator with universal
   constant `1`:
   `‖criticalOperator^2 - G^2‖ ≤ hsNorm (criticalOperator^2 - G^2) ≤ √Δ(G)`
   and drives `1 - P → 0` strongly on every shell (`‖(1 - P) e_n‖ ≤ n √Δ(G)`), yet `‖1 - P‖ = 1`
   whenever `G ≠ criticalOperator`. Tilted high-shell omissions `e_M + ε · packet 1` (`ε ↓ 0⁺`)
   satisfy `Δ → M^{-2}` and `‖criticalOperator^2 - G^2‖ / √Δ → 1`, proving global sharpness of both
   exponent `1 / 2` and constant `1`.
3. **High-temperature self-overlap trichotomy and unified one-sided residual elimination above `84.5`
   (`tendsto_self_overlap_zero_of_half_lt_re`, `tendsto_norm_self_overlap_atTop_of_re_lt_half`,
   `joint_partition_zero_conserves_below_eightyFour_and_half`,
   `rh_iff_unified_residual_elimination_above_eightyFour_and_half`)**: as `v ↓ 0⁺`,
   `ComplementaryHalves.overlap t j a s s v` tends to `0` for `Re s > 1/2`, to `C^s ≠ 0` for
   `Re s = 1/2`, and blows up in norm for `Re s < 1/2`. Strip zeros of `continued` with
   `|Im s| ≤ 169 / 2` unconditionally conserve probability, `continued` is nonvanishing outside
   `[3001/24000, 20999/24000]`, and functional reflection collapses two-sided thermal conservation
   above `84.5` to a single one-sided non-blow-up condition equivalent to `RiemannHypothesis` and
   to the intrinsic Möbius shell margin on `{1/2 < Re w ≤ 20999/24000 ∧ 169/2 < |Im w|}`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open ContinuousLinearMap Filter InnerProductSpace Set Topology
open InverseSpectrum.ShellMixing
open AntipodalSpectrum AntipodalSpectrum.ComplementaryHalves
open CutoffSeparation
open scoped ComplexConjugate InnerProductSpace BigOperators ENNReal

/-! ### Part 1: Trace-free commutant and shell-diagonal rigidity of positive conserving propagators -/

private theorem critical_apply_single (n : ℕ+) :
    criticalOperator (lp.single 2 n (1 : ℂ)) = (attenuation n : ℂ) • lp.single 2 n (1 : ℂ) := by
  apply lp.ext; funext m
  rw [critical_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  by_cases h : m = n
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

private theorem critical_apply_gain_single (n : ℕ+) :
    criticalOperator ((gain n : ℂ) • lp.single 2 n (1 : ℂ)) = lp.single 2 n (1 : ℂ) := by
  rw [map_smul, critical_apply_single, smul_smul, ← Complex.ofReal_mul, attenuation,
    mul_inv_cancel₀ (gain_pos n).ne', Complex.ofReal_one, one_smul]

private theorem attenuation_injective : Function.Injective attenuation := by
  intro m n h
  have hg : gain m = gain n := inv_injective h
  have hsq : (m.val : ℝ) = (n.val : ℝ) := by rw [← gain_sq m, ← gain_sq n, hg]
  exact PNat.coe_injective (Nat.cast_injective hsq)

private theorem inner_single_left_apply (n : ℕ+) (f : Gas) :
    inner ℂ (lp.single 2 n (1 : ℂ)) f = f n := by
  rw [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

/-- Squared-commutant rigidity: any positive conserving propagator `G` whose square commutes with
`criticalOperator` equals `criticalOperator` with no trace hypothesis. -/
theorem sq_commuting_positive_conserving_eq_critical {G : GasOp}
    (hpos : G.IsPositive) (hcons : Conserving G)
    (hcomm : G ^ 2 * criticalOperator = criticalOperator * G ^ 2) :
    G = criticalOperator := by
  obtain ⟨P, ⟨hPD_inj, hG_eq⟩, _⟩ := (positive_propagators_iff G).mp ⟨hpos, hcons⟩
  have hsq : G ^ 2 = criticalOperator * (P.val * criticalOperator) := by
    rw [hG_eq, projected_square]
  have hD_sa : star criticalOperator = criticalOperator := critical_isPositive.isSelfAdjoint.star_eq
  have hP_sa : star P.val = P.val := P.property.isSelfAdjoint.star_eq
  have hleft : ∀ A B : GasOp, criticalOperator * A = criticalOperator * B → A = B :=
    fun A B he => ContinuousLinearMap.ext fun f =>
      critical_injective (congrArg (fun T : GasOp => T f) he)
  have hc1 : (P.val * criticalOperator) * criticalOperator =
      (criticalOperator * P.val) * criticalOperator := by
    apply hleft
    calc criticalOperator * ((P.val * criticalOperator) * criticalOperator)
        = G ^ 2 * criticalOperator := by rw [hsq]; noncomm_ring
      _ = criticalOperator * G ^ 2 := hcomm
      _ = criticalOperator * ((criticalOperator * P.val) * criticalOperator) := by
          rw [hsq]; noncomm_ring
  have hc2 : criticalOperator * (criticalOperator * P.val) =
      criticalOperator * (P.val * criticalOperator) := by
    have hs := congrArg star hc1
    simpa only [star_mul, hD_sa, hP_sa, mul_assoc] using hs
  have hPD_eq : P.val * criticalOperator = criticalOperator * P.val := (hleft _ _ hc2).symm
  have hP_single : ∀ n : ℕ+, P.val (lp.single 2 n (1 : ℂ)) = lp.single 2 n (1 : ℂ) := by
    intro n
    set en : Gas := lp.single 2 n (1 : ℂ)
    have heig : criticalOperator (P.val en) = (attenuation n : ℂ) • P.val en := by
      have h := congrArg (fun T : GasOp => T en) hPD_eq.symm
      change criticalOperator (P.val en) = P.val (criticalOperator en) at h
      rw [h, critical_apply_single, map_smul]
    have hoff : ∀ m : ℕ+, m ≠ n → P.val en m = 0 := by
      intro m hmn
      have hm := congrArg (fun v : Gas => v m) heig
      rw [critical_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hm
      have hsub : ((attenuation m : ℂ) - (attenuation n : ℂ)) * P.val en m = 0 := by
        linear_combination hm
      have hne : (attenuation m : ℂ) - (attenuation n : ℂ) ≠ 0 :=
        sub_ne_zero.mpr fun ha => hmn (attenuation_injective (Complex.ofReal_injective ha))
      exact (mul_eq_zero.mp hsub).resolve_left hne
    have hdiag : P.val en = (P.val en n) • en := by
      apply lp.ext; funext m
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      by_cases hmn : m = n
      · subst hmn; simp [en]
      · rw [hoff m hmn, lp.single_apply, Pi.single_eq_of_ne hmn, mul_zero]
    set c : ℂ := P.val en n
    have hc_idem : c * c = c := by
      have hp2 : P.val (P.val en) = P.val en :=
        congrArg (fun T : GasOp => T en) P.property.isIdempotentElem.eq
      rw [hdiag, map_smul, ← hdiag, hdiag, smul_smul] at hp2
      have hpn := congrArg (fun v : Gas => v n) hp2
      simpa [en] using hpn
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hP0 : P.val en = 0 := by rw [hdiag, hc0, zero_smul]
      have hinj : (P.val * criticalOperator) ((gain n : ℂ) • en) =
          (P.val * criticalOperator) 0 := by
        change P.val (criticalOperator ((gain n : ℂ) • en)) = P.val (criticalOperator 0)
        rw [critical_apply_gain_single, hP0, map_zero, map_zero]
      have hzero := hPD_inj hinj
      have hn := congrArg (fun v : Gas => v n) hzero
      simp only [en, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply,
        Pi.single_eq_same, mul_one, lp.coeFn_zero, Pi.zero_apply] at hn
      exact (Complex.ofReal_ne_zero.mpr (gain_pos n).ne') hn
    have hc1' : c = 1 := mul_left_cancel₀ hc_ne (hc_idem.trans (mul_one c).symm)
    rw [hdiag, hc1', one_smul]
  have hP_one : P.val = 1 := by
    apply ContinuousLinearMap.ext; intro f; apply lp.ext; funext n
    rw [one_apply_eq_self (F := GasOp), ← inner_single_left_apply n (P.val f),
      ← adjoint_inner_left P.val f (lp.single 2 n (1 : ℂ)),
      show adjoint P.val = P.val from hP_sa, hP_single n, inner_single_left_apply]
  exact hG_eq.trans ((projected_eq_critical_iff P).mpr hP_one)

/-- **Trace-free commutant rigidity:** positivity, cyclic-order conservation, and commutation with
`criticalOperator` characterize `criticalOperator` exactly, eliminating all noncanonical conserving
approximants without any trace reading. -/
theorem commuting_positive_conserving_iff_eq_critical (G : GasOp) :
    G.IsPositive ∧ Conserving G ∧ G * criticalOperator = criticalOperator * G ↔
      G = criticalOperator := by
  constructor
  · rintro ⟨hpos, hcons, hcomm⟩
    apply sq_commuting_positive_conserving_eq_critical hpos hcons
    calc G ^ 2 * criticalOperator
        = G * (G * criticalOperator) := by rw [pow_two, mul_assoc]
      _ = G * (criticalOperator * G) := by rw [hcomm]
      _ = (G * criticalOperator) * G := by rw [mul_assoc]
      _ = criticalOperator * G ^ 2 := by rw [hcomm, pow_two, mul_assoc]
  · rintro rfl
    refine ⟨critical_isPositive, ?_, rfl⟩
    have h := conserves_factor (LinearIsometry.id : Gas →ₗᵢ[ℂ] Gas)
    change Conserving (criticalOperator * 1) at h
    rwa [mul_one] at h

/-- **Universal shell mixing of noncanonical positive conserving propagators:** every positive
conserving `G ≠ criticalOperator` (not merely rank-one packet omissions) must connect at least one
pair of distinct occupation shells in `G^2`. -/
theorem noncanonical_positive_conserving_breaks_shell_diagonal {G : GasOp}
    (hpos : G.IsPositive) (hcons : Conserving G) (hne : G ≠ criticalOperator) :
    ∃ m n : ℕ+, m ≠ n ∧ (G ^ 2) (lp.single 2 n (1 : ℂ)) m ≠ 0 := by
  by_contra hdiag_all
  push Not at hdiag_all
  apply hne
  apply sq_commuting_positive_conserving_eq_critical hpos hcons
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (HilbertSchmidt.lpBasis ℕ+).dense_span) ?_
  rintro _ ⟨n, rfl⟩
  rw [HilbertSchmidt.lpBasis_apply]
  set en : Gas := lp.single 2 n (1 : ℂ)
  have hG2_en : (G ^ 2) en = ((G ^ 2) en n) • en := by
    apply lp.ext; funext m
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hmn : m = n
    · subst hmn; simp [en]
    · rw [hdiag_all m n hmn, lp.single_apply, Pi.single_eq_of_ne hmn, mul_zero]
  change (G ^ 2) (criticalOperator en) = criticalOperator ((G ^ 2) en)
  rw [critical_apply_single, map_smul, hG2_en, map_smul, critical_apply_single,
    smul_smul, smul_smul, mul_comm]

/-! ### Part 2: Sharp constant-`1` `ζ(2)` fourth-trace stability vs. unit range-defect norm -/

private theorem critical_sq_sub_sq_hs {G : GasOp} (hpos : G.IsPositive) (hcons : Conserving G) :
    (criticalOperator ^ 2 - G ^ 2).IsHilbertSchmidt := by
  obtain ⟨U, hGU, _⟩ := (full_isometry_iff G).mp hcons
  let V := U.toContinuousLinearMap
  have hG_sa : star G = G := hpos.isSelfAdjoint.star_eq
  have hD_sa : star criticalOperator = criticalOperator := critical_isPositive.isSelfAdjoint.star_eq
  have hG2 : G ^ 2 = star V * (squareHeat.val * V) := by
    calc G ^ 2 = star G * G := by rw [hG_sa, pow_two]
      _ = star (criticalOperator * V) * (criticalOperator * V) := by rw [hGU]
      _ = star V * (squareHeat.val * V) := by
          rw [star_mul, hD_sa]
          change _ = star V * (criticalOperator ^ 2 * V)
          noncomm_ring
  change (squareHeat.val - G ^ 2).IsHilbertSchmidt
  rw [hG2]
  exact squareHeat.property.2.sub ((squareHeat.property.2.comp_right V).comp_left (star V))

/-- **Universal constant-`1` Hilbert–Schmidt stability of squared positive conserving propagators:**
for every positive conserving `G`, `hsNormSq (criticalOperator^2 - G^2)` is at most the fourth-trace
deficit `(riemannZeta 2).re - (opTrace (G^4)).re`. -/
theorem hsNormSq_critical_sq_sub_sq_le_fourth_trace_defect {G : GasOp}
    (hpos : G.IsPositive) (hcons : Conserving G) :
    hsNormSq (criticalOperator ^ 2 - G ^ 2) ≤ (riemannZeta 2).re - (opTrace (G ^ 4)).re := by
  obtain ⟨U, hGU, _⟩ := (full_isometry_iff G).mp hcons
  let V := U.toContinuousLinearMap
  let Q := omitted U
  let A := squareHeat.val
  let E := criticalOperator ^ 2 - G ^ 2
  have hG_sa : star G = G := hpos.isSelfAdjoint.star_eq
  have hD_sa : star criticalOperator = criticalOperator := critical_isPositive.isSelfAdjoint.star_eq
  have hQ_sa : adjoint Q = Q := omitted_self U
  have hE_eq : E = criticalOperator * (Q * criticalOperator) := by
    have hG2_out : G ^ 2 = criticalOperator * ((V * star V) * criticalOperator) := by
      calc G ^ 2 = G * star G := by rw [hG_sa, pow_two]
        _ = (criticalOperator * V) * star (criticalOperator * V) := by rw [hGU]
        _ = criticalOperator * ((V * star V) * criticalOperator) := by
            rw [star_mul, hD_sa]; noncomm_ring
    change criticalOperator ^ 2 - G ^ 2 = criticalOperator * ((1 - V * star V) * criticalOperator)
    rw [hG2_out, pow_two]; noncomm_ring
  have hE_hs : E.IsHilbertSchmidt := critical_sq_sub_sq_hs hpos hcons
  have hQA_hs : (Q * A).IsHilbertSchmidt := squareHeat.property.2.comp_left Q
  let b := HilbertSchmidt.lpBasis ℕ+
  have hQ_symm : ∀ n m : ℕ+, ‖Q (b n) m‖ ^ 2 = ‖Q (b m) n‖ ^ 2 := by
    intro n m
    have h1 : Q (b n) m = conj (Q (b m) n) := by
      rw [HilbertSchmidt.lpBasis_apply, HilbertSchmidt.lpBasis_apply,
        ← inner_single_left_apply m (Q _), ← adjoint_inner_left Q _ _, hQ_sa,
        ← inner_conj_symm (Q _) _, inner_single_left_apply]
    rw [h1, Complex.norm_conj]
  have hE_entry : ∀ n m : ℕ+,
      ‖E (b n) m‖ ^ 2 = attenuation m ^ 2 * attenuation n ^ 2 * ‖Q (b n) m‖ ^ 2 := by
    intro n m
    have hb_eq : b n = lp.single 2 n (1 : ℂ) := HilbertSchmidt.lpBasis_apply n
    have hval : E (b n) m = (attenuation n : ℂ) * ((attenuation m : ℂ) * Q (b n) m) := by
      rw [hE_eq]
      change criticalOperator (Q (criticalOperator (b n))) m = _
      rw [hb_eq, critical_apply_single, map_smul, map_smul, lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul, critical_apply, ← hb_eq]
    rw [hval, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (attenuation_pos n).le, Real.norm_of_nonneg (attenuation_pos m).le]
    ring
  have hQA_entry : ∀ n m : ℕ+,
      ‖(Q * A) (b n) m‖ ^ 2 = attenuation n ^ 4 * ‖Q (b n) m‖ ^ 2 := by
    intro n m
    have hb_eq : b n = lp.single 2 n (1 : ℂ) := HilbertSchmidt.lpBasis_apply n
    have hA_bn : A (b n) = ((attenuation n ^ 2 : ℝ) : ℂ) • b n := by
      change (criticalOperator ^ 2) (b n) = _
      rw [pow_two]
      change criticalOperator (criticalOperator (b n)) = _
      rw [hb_eq, critical_apply_single, map_smul, critical_apply_single, smul_smul,
        ← Complex.ofReal_mul, ← pow_two]
    have hval : (Q * A) (b n) m = ((attenuation n ^ 2 : ℝ) : ℂ) * Q (b n) m := by
      change Q (A (b n)) m = _
      rw [hA_bn, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [hval, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    ring
  -- Compare `2 * hsNormSq E` against `2 * hsNormSq (Q * A)` in `ℝ≥0∞` via `ENNReal.tsum_comm`.
  have hENN_E : ENNReal.ofReal (2 * hsNormSq E) =
      ∑' n : ℕ+, ∑' m : ℕ+,
        ENNReal.ofReal (2 * (attenuation m ^ 2 * attenuation n ^ 2 * ‖Q (b n) m‖ ^ 2)) := by
    rw [hsNormSq_eq hE_hs b, ← (hE_hs.summable b).tsum_mul_left,
      ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) ((hE_hs.summable b).mul_left 2)]
    refine tsum_congr fun n => ?_
    rw [HTGeometry.lp_norm_sq_eq_tsum (E (b n)),
      ← (HTGeometry.lp_summable_norm_sq (E (b n))).tsum_mul_left,
      ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity)
        ((HTGeometry.lp_summable_norm_sq (E (b n))).mul_left 2)]
    exact tsum_congr fun m => by rw [hE_entry]
  have hENN_QA : ENNReal.ofReal (hsNormSq (Q * A)) =
      ∑' n : ℕ+, ∑' m : ℕ+, ENNReal.ofReal (attenuation n ^ 4 * ‖Q (b n) m‖ ^ 2) := by
    rw [hsNormSq_eq hQA_hs b,
      ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hQA_hs.summable b)]
    refine tsum_congr fun n => ?_
    rw [HTGeometry.lp_norm_sq_eq_tsum ((Q * A) (b n)),
      ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity)
        (HTGeometry.lp_summable_norm_sq ((Q * A) (b n)))]
    exact tsum_congr fun m => by rw [hQA_entry]
  have hENN_le : ENNReal.ofReal (2 * hsNormSq E) ≤ ENNReal.ofReal (2 * hsNormSq (Q * A)) := by
    rw [hENN_E]
    have hpt : ∀ n m : ℕ+,
        ENNReal.ofReal (2 * (attenuation m ^ 2 * attenuation n ^ 2 * ‖Q (b n) m‖ ^ 2)) ≤
          ENNReal.ofReal (attenuation m ^ 4 * ‖Q (b m) n‖ ^ 2) +
            ENNReal.ofReal (attenuation n ^ 4 * ‖Q (b n) m‖ ^ 2) := by
      intro n m
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← hQ_symm n m]
      nlinarith [sq_nonneg (attenuation m ^ 2 - attenuation n ^ 2), sq_nonneg ‖Q (b n) m‖]
    calc (∑' n : ℕ+, ∑' m : ℕ+,
            ENNReal.ofReal (2 * (attenuation m ^ 2 * attenuation n ^ 2 * ‖Q (b n) m‖ ^ 2)))
        ≤ ∑' n : ℕ+, ∑' m : ℕ+,
            (ENNReal.ofReal (attenuation m ^ 4 * ‖Q (b m) n‖ ^ 2) +
              ENNReal.ofReal (attenuation n ^ 4 * ‖Q (b n) m‖ ^ 2)) :=
          ENNReal.tsum_le_tsum fun n => ENNReal.tsum_le_tsum fun m => hpt n m
      _ = (∑' n : ℕ+, ∑' m : ℕ+, ENNReal.ofReal (attenuation m ^ 4 * ‖Q (b m) n‖ ^ 2)) +
            (∑' n : ℕ+, ∑' m : ℕ+, ENNReal.ofReal (attenuation n ^ 4 * ‖Q (b n) m‖ ^ 2)) := by
          simp_rw [ENNReal.tsum_add]
      _ = ENNReal.ofReal (hsNormSq (Q * A)) + ENNReal.ofReal (hsNormSq (Q * A)) := by
          rw [ENNReal.tsum_comm (f := fun n m : ℕ+ =>
            ENNReal.ofReal (attenuation m ^ 4 * ‖Q (b m) n‖ ^ 2)), ← hENN_QA]
      _ = ENNReal.ofReal (2 * hsNormSq (Q * A)) := by
          rw [← ENNReal.ofReal_add (hsNormSq_nonneg _) (hsNormSq_nonneg _), two_mul]
  have hreal_le : 2 * hsNormSq E ≤ 2 * hsNormSq (Q * A) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg zero_le_two (hsNormSq_nonneg _))).mp hENN_le
  have hdef := fourth_trace_defect U
  rw [← hGU, fourthMoment_of_positive hpos] at hdef
  linarith [hreal_le, hdef, hsNormSq_nonneg (Q * (A * V))]

private theorem cancel_critical_both {X Y : GasOp}
    (h : criticalOperator * (X * criticalOperator) = criticalOperator * (Y * criticalOperator)) :
    X = Y := by
  have hD_sa : star criticalOperator = criticalOperator := critical_isPositive.isSelfAdjoint.star_eq
  have hleft : ∀ A B : GasOp, criticalOperator * A = criticalOperator * B → A = B :=
    fun A B he => ContinuousLinearMap.ext fun f =>
      critical_injective (congrArg (fun T : GasOp => T f) he)
  have hr := hleft _ _ h
  have hs : criticalOperator * star X = criticalOperator * star Y := by
    have h1 := congrArg star hr
    rwa [star_mul, star_mul, hD_sa] at h1
  exact star_injective (hleft _ _ hs)

/-- **Sharp constant-`1` operator-norm stability and shellwise strong convergence:** for every
positive conserving `G = projected P`, `‖criticalOperator^2 - G^2‖ ≤ √Δ(G)` and on every shell `n`,
`‖(1 - P.val) e_n‖ ≤ n √Δ(G)`. -/
theorem norm_critical_sq_sub_sq_le_sqrt_fourth_trace_defect {P : Projection}
    (hcons : Conserving (projected P)) :
    ‖criticalOperator ^ 2 - (projected P) ^ 2‖ ≤ hsNorm (criticalOperator ^ 2 - (projected P) ^ 2) ∧
      hsNorm (criticalOperator ^ 2 - (projected P) ^ 2) ≤
        Real.sqrt ((riemannZeta 2).re - (opTrace ((projected P) ^ 4)).re) ∧
      ∀ n : ℕ+, ‖((1 : GasOp) - P.val) (lp.single 2 n (1 : ℂ))‖ ≤
        (n.val : ℝ) * Real.sqrt ((riemannZeta 2).re - (opTrace ((projected P) ^ 4)).re) := by
  have hpos : (projected P).IsPositive := projected_positive P
  have hsq1 : (projected P) ^ 2 = criticalOperator * (P.val * criticalOperator) := projected_square P
  -- Generalize `projected P` to an opaque variable `G : GasOp` so `positiveRoot` is never unfolded.
  generalize projected P = G at hcons hpos hsq1 ⊢
  have hE_hs := critical_sq_sub_sq_hs hpos hcons
  have hhs_le := hsNormSq_critical_sq_sub_sq_le_fourth_trace_defect hpos hcons
  refine ⟨opNorm_le_hsNorm hE_hs, Real.sqrt_le_sqrt hhs_le, fun n => ?_⟩
  obtain ⟨U, hGU, _⟩ := (full_isometry_iff G).mp hcons
  have hD_sa : star criticalOperator = criticalOperator := critical_isPositive.isSelfAdjoint.star_eq
  have hG_sa : star G = G := hpos.isSelfAdjoint.star_eq
  have hsq2 : G ^ 2 =
      criticalOperator * ((U.toContinuousLinearMap * star U.toContinuousLinearMap) * criticalOperator) := by
    calc G ^ 2 = G * star G := by rw [hG_sa, pow_two]
      _ = (criticalOperator * U.toContinuousLinearMap) *
            star (criticalOperator * U.toContinuousLinearMap) := by rw [hGU]
      _ = criticalOperator *
            ((U.toContinuousLinearMap * star U.toContinuousLinearMap) * criticalOperator) := by
          rw [star_mul, hD_sa]; noncomm_ring
  have hP_eq : P.val = U.toContinuousLinearMap * star U.toContinuousLinearMap :=
    cancel_critical_both (hsq1.symm.trans hsq2)
  have h1P : (1 : GasOp) - P.val = omitted U := by rw [hP_eq]; rfl
  rw [h1P]
  have hQA_hs : (omitted U * squareHeat.val).IsHilbertSchmidt :=
    squareHeat.property.2.comp_left (omitted U)
  have hterm_le : ‖(omitted U * squareHeat.val) (HilbertSchmidt.lpBasis ℕ+ n)‖ ^ 2 ≤
      hsNormSq (omitted U * squareHeat.val) := by
    rw [hsNormSq_eq hQA_hs (HilbertSchmidt.lpBasis ℕ+)]
    exact Summable.le_tsum (hQA_hs.summable (HilbertSchmidt.lpBasis ℕ+)) n (fun _ _ => sq_nonneg _)
  have hdef := fourth_trace_defect U
  rw [← hGU, fourthMoment_of_positive hpos] at hdef
  have hQA_le_Δ : hsNormSq (omitted U * squareHeat.val) ≤
      (riemannZeta 2).re - (opTrace (G ^ 4)).re := by
    linarith [hdef, hsNormSq_nonneg (omitted U * (squareHeat.val * U.toContinuousLinearMap))]
  have hA_bn : (omitted U * squareHeat.val) (HilbertSchmidt.lpBasis ℕ+ n) =
      (((n.val : ℝ)⁻¹ : ℝ) : ℂ) • omitted U (lp.single 2 n (1 : ℂ)) := by
    rw [HilbertSchmidt.lpBasis_apply]
    change omitted U ((criticalOperator ^ 2) (lp.single 2 n (1 : ℂ))) = _
    rw [pow_two]
    change omitted U (criticalOperator (criticalOperator (lp.single 2 n (1 : ℂ)))) = _
    rw [critical_apply_single, map_smul, critical_apply_single, smul_smul, ← Complex.ofReal_mul,
      attenuation, ← pow_two, inv_pow, gain_sq, map_smul]
  have hn_pos : (0 : ℝ) < n.val := Nat.cast_pos.mpr n.pos
  have hnorm_QA : ‖(omitted U * squareHeat.val) (HilbertSchmidt.lpBasis ℕ+ n)‖ =
      (n.val : ℝ)⁻¹ * ‖omitted U (lp.single 2 n (1 : ℂ))‖ := by
    rw [hA_bn, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hn_pos.le)]
  have hnorm_le_sqrt : ‖(omitted U * squareHeat.val) (HilbertSchmidt.lpBasis ℕ+ n)‖ ≤
      Real.sqrt ((riemannZeta 2).re - (opTrace (G ^ 4)).re) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (hterm_le.trans hQA_le_Δ)
  rw [hnorm_QA] at hnorm_le_sqrt
  have hmul := mul_le_mul_of_nonneg_left hnorm_le_sqrt hn_pos.le
  rwa [← mul_assoc, mul_inv_cancel₀ hn_pos.ne', one_mul] at hmul

/-- **Unit range-defect instability:** for every noncanonical positive conserving propagator
`projected P ≠ criticalOperator`, the missing-range projection `1 - P.val` has exact operator norm `1`. -/
theorem norm_omitted_eq_one_of_ne_critical {P : Projection}
    (hne : projected P ≠ criticalOperator) :
    ‖(1 : GasOp) - P.val‖ = 1 := by
  set Q : GasOp := (1 : GasOp) - P.val
  have hQ_proj : IsStarProjection Q := P.property.one_sub
  have hQ_sa : adjoint Q = Q := hQ_proj.isSelfAdjoint.star_eq
  have hQ_idem : Q * Q = Q := hQ_proj.isIdempotentElem.eq
  have hQ_ne : Q ≠ 0 := sub_ne_zero.mpr fun h1 => hne ((projected_eq_critical_iff P).mpr h1.symm)
  apply le_antisymm
  · refine opNorm_le_bound Q zero_le_one fun x => ?_
    rw [one_mul]
    by_cases hx0 : ‖Q x‖ = 0
    · rw [hx0]; exact norm_nonneg x
    · have hpos : 0 < ‖Q x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)
      have hsq : ‖Q x‖ ^ 2 ≤ ‖x‖ * ‖Q x‖ := by
        calc ‖Q x‖ ^ 2 = (inner ℂ (Q x) (Q x)).re := (inner_self_eq_norm_sq (𝕜 := ℂ) (Q x)).symm
          _ = (inner ℂ x (Q (Q x))).re := by
              rw [← adjoint_inner_left Q (Q x) x, hQ_sa]
          _ = (inner ℂ x (Q x)).re := by
              have hqq := congrArg (fun T : GasOp => T x) hQ_idem
              change Q (Q x) = Q x at hqq; rw [hqq]
          _ ≤ ‖inner ℂ x (Q x)‖ := Complex.re_le_norm _
          _ ≤ ‖x‖ * ‖Q x‖ := norm_inner_le_norm x (Q x)
      nlinarith
  · have hex : ∃ x : Gas, Q x ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hQ_ne (ContinuousLinearMap.ext fun x => hall x)
    obtain ⟨x, hx⟩ := hex
    set y := Q x
    have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hx
    have hQy : Q y = y := congrArg (fun T : GasOp => T x) hQ_idem
    have hle := Q.le_opNorm y
    rw [hQy] at hle
    nlinarith

/-- High-shell vector `e_M + ε · packet 1` tilted out of `Set.range criticalOperator`. -/
def tiltedShellVector (M : ℕ+) (ε : ℝ) : Gas :=
  lp.single 2 M (1 : ℂ) + (ε : ℂ) • packet ⟨1, by norm_num⟩

/-- Positive conserving propagator omitting `tiltedShellVector M ε`. -/
def tiltedShellPropagator (M : ℕ+) (ε : PacketScale) : GasOp :=
  projected (omitLine (tiltedShellVector M ε.val))

private theorem tiltedShellVector_not_mem_range (M : ℕ+) {ε : ℝ} (hε : ε ≠ 0) :
    tiltedShellVector M ε ∉ Set.range criticalOperator := by
  rintro ⟨f, hf⟩
  have h1_not : packet ⟨1, by norm_num⟩ ∉ Set.range criticalOperator := by
    rw [packet_in_range_iff]; norm_num
  apply h1_not
  refine ⟨(ε : ℂ)⁻¹ • (f - (gain M : ℂ) • lp.single 2 M (1 : ℂ)), ?_⟩
  rw [map_smul, map_sub, hf, critical_apply_gain_single]
  unfold tiltedShellVector
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hε), one_smul]

private theorem tiltedShellVector_ne_zero (M : ℕ+) {ε : ℝ} (hε : ε ≠ 0) :
    tiltedShellVector M ε ≠ 0 := by
  intro hz
  exact tiltedShellVector_not_mem_range M hε ⟨0, by rw [map_zero, hz]⟩

private theorem omitLine_square_eq {v : Gas} (_hv : v ≠ 0) :
    (projected (omitLine v)) ^ 2 =
      squareHeat.val - (((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹) • rankOne ℂ (criticalOperator v) (criticalOperator v) := by
  rw [projected_square]
  have hD_sa : adjoint criticalOperator = criticalOperator := critical_isPositive.isSelfAdjoint.star_eq
  apply ContinuousLinearMap.ext; intro f
  change criticalOperator ((ℂ ∙ v)ᗮ.starProjection (criticalOperator f)) =
    criticalOperator (criticalOperator f) -
      (((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹) • ((inner ℂ (criticalOperator v) f) • criticalOperator v)
  rw [Submodule.starProjection_orthogonal', sub_apply, one_apply_eq_self (F := GasOp),
    Submodule.starProjection_singleton, map_sub, map_smul, div_eq_inv_mul, mul_smul,
    ← adjoint_inner_left criticalOperator f v, hD_sa]; rfl

/-- Every `tiltedShellPropagator M ε` (`ε > 0`) is positive, conserving, and strictly noncanonical
with unit range-defect norm `1`. -/
theorem tiltedShellPropagator_properties (M : ℕ+) (ε : PacketScale) :
    (tiltedShellPropagator M ε).IsPositive ∧
      Conserving (tiltedShellPropagator M ε) ∧
      tiltedShellPropagator M ε ≠ criticalOperator ∧
      ‖(1 : GasOp) - (omitLine (tiltedShellVector M ε.val)).val‖ = 1 := by
  have hε_ne : ε.val ≠ 0 := ε.property.ne'
  set v := tiltedShellVector M ε.val
  have hv_out := tiltedShellVector_not_mem_range M hε_ne
  have hv_ne := tiltedShellVector_ne_zero M hε_ne
  have hcons : Conserving (projected (omitLine v)) := by
    rw [projected_conserves_iff]
    intro x y hxy
    have hz : (omitLine v).val (criticalOperator (x - y)) = 0 := by
      change (omitLine v).val (criticalOperator x) = (omitLine v).val (criticalOperator y) at hxy
      rw [map_sub, map_sub, hxy, sub_self]
    have hmem : criticalOperator (x - y) ∈ ℂ ∙ v := by
      have hm : criticalOperator (x - y) ∈ (ℂ ∙ v)ᗮ.starProjection.toLinearMap.ker := hz
      rwa [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal] at hm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    by_cases ha0 : a = 0
    · rw [ha0, zero_smul, map_sub] at ha
      exact critical_injective (sub_eq_zero.mp ha.symm)
    · exfalso
      exact hv_out ⟨a⁻¹ • (x - y), by rw [map_smul, ← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩
  have hne : projected (omitLine v) ≠ criticalOperator := by
    intro h
    have hI := (projected_eq_critical_iff _).mp h
    have hk := omitLine_kills v
    rw [hI] at hk
    exact hv_ne hk
  exact ⟨projected_positive _, hcons, hne, norm_omitted_eq_one_of_ne_critical hne⟩

/-- **Global sharpness of exponent `1 / 2` and universal constant `1`:** for every shell `M : ℕ+`,
as `ε ↓ 0⁺`, the fourth-trace deficit `Δ(tiltedShellPropagator M ε)` converges to `(M.val : ℝ)^{-2} > 0`
and the stability ratio `‖criticalOperator^2 - (tiltedShellPropagator M ε)^2‖ / √Δ` converges to `1`. -/
theorem tendsto_tiltedShell_stability_ratio_one (M : ℕ+) :
    Tendsto (fun ε : PacketScale =>
      (riemannZeta 2).re - (opTrace ((tiltedShellPropagator M ε) ^ 4)).re)
      packetPole (𝓝 (((M.val : ℝ) ^ 2)⁻¹)) ∧
    Tendsto (fun ε : PacketScale =>
      ‖criticalOperator ^ 2 - (tiltedShellPropagator M ε) ^ 2‖ /
        Real.sqrt ((riemannZeta 2).re - (opTrace ((tiltedShellPropagator M ε) ^ 4)).re))
      packetPole (𝓝 1) := by
  set eM : Gas := lp.single 2 M (1 : ℂ)
  set p₁ : Gas := packet ⟨1, by norm_num⟩
  have hM_pos : (0 : ℝ) < M.val := Nat.cast_pos.mpr M.pos
  have heps0 : Tendsto (fun ε : PacketScale => (ε.val : ℂ)) packetPole (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp (tendsto_comap.mono_right nhdsWithin_le_nhds)
  have hv_lim : Tendsto (fun ε : PacketScale => tiltedShellVector M ε.val) packetPole (𝓝 eM) := by
    simpa only [tiltedShellVector, zero_smul, add_zero] using
      (tendsto_const_nhds (x := eM)).add (heps0.smul_const p₁)
  have hDv_lim : Tendsto (fun ε : PacketScale => criticalOperator (tiltedShellVector M ε.val))
      packetPole (𝓝 (criticalOperator eM)) :=
    (criticalOperator.continuous.tendsto eM).comp hv_lim
  have hADv_lim : Tendsto (fun ε : PacketScale =>
      squareHeat.val (criticalOperator (tiltedShellVector M ε.val)))
      packetPole (𝓝 (squareHeat.val (criticalOperator eM))) :=
    (squareHeat.val.continuous.tendsto _).comp hDv_lim
  -- Evaluate the limiting norms and inner product at `eM`.
  have heM_norm : ‖eM‖ ^ 2 = 1 := by
    dsimp only [eM]; rw [lp.norm_single (by norm_num), norm_one, one_pow]
  have hDeM_norm : ‖criticalOperator eM‖ ^ 2 = (M.val : ℝ)⁻¹ := by
    dsimp only [eM]
    rw [critical_apply_single, norm_smul, lp.norm_single (by norm_num), norm_one, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (attenuation_pos M).le, attenuation,
      inv_pow, gain_sq]
  have hDeM_inner : (inner ℂ (criticalOperator eM) (squareHeat.val (criticalOperator eM))).re =
      ((M.val : ℝ) ^ 2)⁻¹ := by
    dsimp only [eM]
    change (inner ℂ (criticalOperator (lp.single 2 M (1 : ℂ)))
      ((criticalOperator ^ 2) (criticalOperator (lp.single 2 M (1 : ℂ))))).re = _
    rw [pow_two]
    change (inner ℂ (criticalOperator (lp.single 2 M (1 : ℂ)))
      (criticalOperator (criticalOperator (criticalOperator (lp.single 2 M (1 : ℂ)))))).re = _
    rw [critical_apply_single, map_smul, critical_apply_single, map_smul, map_smul,
      critical_apply_single, smul_smul, smul_smul, inner_smul_left, inner_smul_right,
      inner_single_left_apply, lp.single_apply, Pi.single_eq_same, mul_one,
      Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re, attenuation]
    have hg : gain M ^ 2 = (M.val : ℝ) := gain_sq M
    have hg_ne : gain M ≠ 0 := (gain_pos M).ne'
    field_simp [hg_ne]
    nlinarith [hg]
  -- Exact rank-one formula for `Δ(ε)`.
  have hΔ_eq : ∀ ε : PacketScale,
      (riemannZeta 2).re - (opTrace ((tiltedShellPropagator M ε) ^ 4)).re =
        2 * (inner ℂ (criticalOperator (tiltedShellVector M ε.val))
            (squareHeat.val (criticalOperator (tiltedShellVector M ε.val)))).re /
          (‖tiltedShellVector M ε.val‖ ^ 2) -
        (‖criticalOperator (tiltedShellVector M ε.val)‖ ^ 2 /
          (‖tiltedShellVector M ε.val‖ ^ 2)) ^ 2 := by
    intro ε
    have hv_ne := tiltedShellVector_ne_zero M ε.property.ne'
    have hsq := omitLine_square_eq hv_ne
    have hp4 : (tiltedShellPropagator M ε) ^ 4 =
        ((projected (omitLine (tiltedShellVector M ε.val))) ^ 2) ^ 2 := by
      rw [tiltedShellPropagator, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    have hsq_tr : (squareHeat.val ^ 2).opTrace = riemannZeta 2 := critical_fourth_trace
    have hw_inner : inner ℂ (criticalOperator (tiltedShellVector M ε.val))
        (criticalOperator (tiltedShellVector M ε.val)) =
        (((‖criticalOperator (tiltedShellVector M ε.val)‖ ^ 2 : ℝ) : ℂ)) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), Complex.ofReal_pow]; rfl
    have htr : opTrace ((tiltedShellPropagator M ε) ^ 4) =
        riemannZeta 2 -
          (((2 * (‖tiltedShellVector M ε.val‖ ^ 2)⁻¹ : ℝ) : ℂ)) *
            inner ℂ (criticalOperator (tiltedShellVector M ε.val))
              (squareHeat.val (criticalOperator (tiltedShellVector M ε.val))) +
          (((((‖tiltedShellVector M ε.val‖ ^ 2)⁻¹ ^ 2 *
            (‖criticalOperator (tiltedShellVector M ε.val)‖ ^ 2) ^ 2 : ℝ) : ℂ))) := by
      rw [hp4, hsq, ← Complex.ofReal_inv,
        rank_one_trace_square squareHeat (criticalOperator (tiltedShellVector M ε.val)) _,
        hsq_tr, hw_inner]
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
    have hre := congrArg Complex.re htr
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hre
    have hnv_ne : ‖tiltedShellVector M ε.val‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hv_ne)
    generalize (opTrace ((tiltedShellPropagator M ε) ^ 4)).re = tr4 at hre ⊢
    generalize (inner ℂ (criticalOperator (tiltedShellVector M ε.val))
      (squareHeat.val (criticalOperator (tiltedShellVector M ε.val)))).re = inn at hre ⊢
    generalize ‖criticalOperator (tiltedShellVector M ε.val)‖ ^ 2 = nw at hre ⊢
    generalize ‖tiltedShellVector M ε.val‖ ^ 2 = nv at hnv_ne hre ⊢
    have halg : 2 * nv⁻¹ * inn - nv⁻¹ ^ 2 * nw ^ 2 = 2 * inn / nv - (nw / nv) ^ 2 := by
      field_simp [hnv_ne]
    linarith [hre, halg]
  have hv_sq_lim : Tendsto (fun ε : PacketScale => ‖tiltedShellVector M ε.val‖ ^ 2)
      packetPole (𝓝 1) := by
    simpa only [heM_norm] using (hv_lim.norm.pow 2)
  have hDv_sq_lim : Tendsto (fun ε : PacketScale =>
      ‖criticalOperator (tiltedShellVector M ε.val)‖ ^ 2) packetPole (𝓝 ((M.val : ℝ)⁻¹)) := by
    simpa only [hDeM_norm] using (hDv_lim.norm.pow 2)
  have hinner_lim : Tendsto (fun ε : PacketScale =>
      (inner ℂ (criticalOperator (tiltedShellVector M ε.val))
        (squareHeat.val (criticalOperator (tiltedShellVector M ε.val)))).re)
      packetPole (𝓝 (((M.val : ℝ) ^ 2)⁻¹)) := by
    have hi : Tendsto (fun ε : PacketScale =>
        inner ℂ (criticalOperator (tiltedShellVector M ε.val))
          (squareHeat.val (criticalOperator (tiltedShellVector M ε.val))))
        packetPole (𝓝 (inner ℂ (criticalOperator eM) (squareHeat.val (criticalOperator eM)))) :=
      Tendsto.inner hDv_lim hADv_lim
    simpa only [hDeM_inner, Function.comp_def] using (Complex.continuous_re.tendsto _).comp hi
  have hΔ_lim : Tendsto (fun ε : PacketScale =>
      (riemannZeta 2).re - (opTrace ((tiltedShellPropagator M ε) ^ 4)).re)
      packetPole (𝓝 (((M.val : ℝ) ^ 2)⁻¹)) := by
    have hterm1 := (hinner_lim.const_mul 2).div hv_sq_lim one_ne_zero
    have hterm2 := (hDv_sq_lim.div hv_sq_lim one_ne_zero).pow 2
    have hdiff := hterm1.sub hterm2
    have hval : 2 * ((M.val : ℝ) ^ 2)⁻¹ / 1 - ((M.val : ℝ)⁻¹ / 1) ^ 2 = ((M.val : ℝ) ^ 2)⁻¹ := by
      field_simp [hM_pos.ne']; ring
    rw [hval] at hdiff
    exact hdiff.congr fun ε => (hΔ_eq ε).symm
  refine ⟨hΔ_lim, ?_⟩
  -- Squeeze `‖D^2 - G^2‖ / √Δ` between `(‖D v‖^2 / ‖v‖^2) / √Δ → 1` and `1`.
  have hsqrt_Δ_lim : Tendsto (fun ε : PacketScale =>
      Real.sqrt ((riemannZeta 2).re - (opTrace ((tiltedShellPropagator M ε) ^ 4)).re))
      packetPole (𝓝 ((M.val : ℝ)⁻¹)) := by
    have hs := (Real.continuous_sqrt.tendsto _).comp hΔ_lim
    have hsq_inv : Real.sqrt (((M.val : ℝ) ^ 2)⁻¹) = (M.val : ℝ)⁻¹ := by
      rw [Real.sqrt_inv, Real.sqrt_sq hM_pos.le]
    simpa only [Function.comp_def, hsq_inv] using hs
  have hlower_lim : Tendsto (fun ε : PacketScale =>
      (‖criticalOperator (tiltedShellVector M ε.val)‖ ^ 2 / ‖tiltedShellVector M ε.val‖ ^ 2) /
        Real.sqrt ((riemannZeta 2).re - (opTrace ((tiltedShellPropagator M ε) ^ 4)).re))
      packetPole (𝓝 1) := by
    have h := (hDv_sq_lim.div hv_sq_lim one_ne_zero).div hsqrt_Δ_lim (inv_ne_zero hM_pos.ne')
    have h1 : ((M.val : ℝ)⁻¹ / 1) / (M.val : ℝ)⁻¹ = 1 := by field_simp [hM_pos.ne']
    rw [h1] at h
    exact h.congr fun _ => rfl
  have hΔ_pos_ev : ∀ᶠ ε : PacketScale in packetPole,
      0 < (riemannZeta 2).re - (opTrace ((tiltedShellPropagator M ε) ^ 4)).re :=
    hΔ_lim.eventually (Ioi_mem_nhds (by positivity : 0 < ((M.val : ℝ) ^ 2)⁻¹))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower_lim tendsto_const_nhds ?_ ?_
  · filter_upwards [hΔ_pos_ev] with ε hΔ_pos
    set v := tiltedShellVector M ε.val
    set w := criticalOperator v
    have hv_ne := tiltedShellVector_ne_zero M ε.property.ne'
    have hw_ne : w ≠ 0 := fun hw0 => hv_ne (critical_injective (hw0.trans (map_zero _).symm))
    have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
    have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    -- Evaluate `D^2 - G^2` on unit vector `‖w‖⁻¹ • w`.
    set u : Gas := ((‖w‖ : ℂ)⁻¹) • w
    have hu_norm : ‖u‖ = 1 := by
      dsimp only [u]
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw_pos,
        inv_mul_cancel₀ hw_pos.ne']
    have hdiff_eq : criticalOperator ^ 2 - (tiltedShellPropagator M ε) ^ 2 =
        (((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹) • rankOne ℂ w w := by
      rw [tiltedShellPropagator, omitLine_square_eq hv_ne]
      exact sub_sub_cancel (criticalOperator ^ 2) _
    have happ : (criticalOperator ^ 2 - (tiltedShellPropagator M ε) ^ 2) u =
        (((‖w‖ / ‖v‖ ^ 2 : ℝ) : ℂ)) • w := by
      rw [hdiff_eq, smul_apply]
      have hr1 : rankOne ℂ w w u = (inner ℂ w u) • w := rfl
      have hwu : inner ℂ w u = (‖w‖ : ℂ) := by
        dsimp only [u]
        rw [inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w]
        have hw_c : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw_pos.ne'
        field_simp [hw_c]; rfl
      rw [hr1, hwu, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul, div_eq_inv_mul]
    have hop_ge : ‖w‖ ^ 2 / ‖v‖ ^ 2 ≤ ‖criticalOperator ^ 2 - (tiltedShellPropagator M ε) ^ 2‖ := by
      have hle := (criticalOperator ^ 2 - (tiltedShellPropagator M ε) ^ 2).le_opNorm u
      rw [hu_norm, mul_one, happ, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)] at hle
      have hrew : ‖w‖ / ‖v‖ ^ 2 * ‖w‖ = ‖w‖ ^ 2 / ‖v‖ ^ 2 := by ring
      rwa [hrew] at hle
    exact div_le_div_of_nonneg_right hop_ge (Real.sqrt_nonneg _)
  · filter_upwards [hΔ_pos_ev] with ε hΔ_pos
    have hcons := (tiltedShellPropagator_properties M ε).2.1
    have hub := norm_critical_sq_sub_sq_le_sqrt_fourth_trace_defect hcons
    exact (div_le_one (Real.sqrt_pos.mpr hΔ_pos)).mpr (hub.1.trans hub.2.1)

/-! ### Part 3: High-temperature `overlap` trichotomy and one-sided partition conservation above `84.5` -/

/-- Exact positive-time norm formula for the complementary self-overlap `overlap t j a s s v`. -/
theorem norm_self_overlap_eq (t : ExceptionalTime) (j : ℕ) (a : ℝ) (s : ℂ)
    {v : ℝ} (hv : 0 < v) :
    ‖AntipodalSpectrum.ComplementaryHalves.overlap t j a s s v‖ =
      (((tailRadix t j).val : ℝ) ^ s.re * (v * kernel (clockRadix t j) a v)) *
        v ^ (2 * s.re - 1) := by
  let C := clockRadix t j
  have hC_pos : (0 : ℝ) < (tailRadix t j).val := Nat.cast_pos.mpr (tailRadix t j).pos
  have hCv_pos : 0 < ((tailRadix t j).val : ℝ) * v := mul_pos hC_pos hv
  have hker_pos : 0 < kernel C a v := by
    unfold kernel
    exact div_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv)))
  have hprod := physical_heat_product t j a ⟨v, hv⟩
  have habs_prod : |cutoffHeat t j a v| * |cutoffHeat t j a (((tailRadix t j).val : ℝ) * v)| =
      kernel C a v := by
    rw [← abs_mul, hprod, abs_of_pos hker_pos]
  unfold AntipodalSpectrum.ComplementaryHalves.overlap reading
  rw [norm_mul, Complex.norm_conj, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hv s,
    Complex.norm_cpow_eq_rpow_re_of_pos hCv_pos s,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hrpow_mul : (((tailRadix t j).val : ℝ) * v) ^ s.re =
      ((tailRadix t j).val : ℝ) ^ s.re * v ^ s.re :=
    Real.mul_rpow hC_pos.le hv.le
  have hrpow_v' : v ^ s.re * v ^ s.re = v * v ^ (2 * s.re - 1) := by
    calc v ^ s.re * v ^ s.re = v ^ (s.re + s.re) := (Real.rpow_add hv s.re s.re).symm
      _ = v ^ ((1 : ℝ) + (2 * s.re - 1)) := by congr 1; ring
      _ = v ^ (1 : ℝ) * v ^ (2 * s.re - 1) := Real.rpow_add hv 1 (2 * s.re - 1)
      _ = v * v ^ (2 * s.re - 1) := by rw [Real.rpow_one]
  calc (v ^ s.re * |cutoffHeat t j a v|) *
          ((((tailRadix t j).val : ℝ) * v) ^ s.re *
            |cutoffHeat t j a (((tailRadix t j).val : ℝ) * v)|)
      = ((tailRadix t j).val : ℝ) ^ s.re * (v ^ s.re * v ^ s.re) *
          (|cutoffHeat t j a v| * |cutoffHeat t j a (((tailRadix t j).val : ℝ) * v)|) := by
        rw [hrpow_mul]; ring
    _ = (((tailRadix t j).val : ℝ) ^ s.re * (v * kernel C a v)) * v ^ (2 * s.re - 1) := by
        rw [hrpow_v', habs_prod]; ring

/-- **Right-half-plane high-temperature dissipation (`Re s > 1 / 2`):** for every `s` with
`1 / 2 < s.re`, the complementary self-overlap vanishes as `v ↓ 0⁺`. -/
theorem tendsto_self_overlap_zero_of_half_lt_re (t : ExceptionalTime) (j : ℕ) (a : ℝ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Tendsto (AntipodalSpectrum.ComplementaryHalves.overlap t j a s s) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let C := clockRadix t j
  have hpre : Tendsto (fun v : ℝ => ((tailRadix t j).val : ℝ) ^ s.re * (v * kernel C a v))
      (𝓝[>] 0) (𝓝 (((tailRadix t j).val : ℝ) ^ s.re)) := by
    simpa only [mul_one] using (kernel_mass C a).const_mul (((tailRadix t j).val : ℝ) ^ s.re)
  have hexp_pos : 0 < 2 * s.re - 1 := by linarith
  have hrpow0 : Tendsto (fun v : ℝ => v ^ (2 * s.re - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun v : ℝ => v ^ (2 * s.re - 1)) 0 :=
      Real.continuousAt_rpow_const 0 (2 * s.re - 1) (Or.inr hexp_pos.le)
    simpa only [Real.zero_rpow hexp_pos.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hpre.mul hrpow0
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (norm_self_overlap_eq t j a s hv).symm

/-- **Left-half-plane high-temperature blow-up (`Re s < 1 / 2`):** for every `s` with `s.re < 1 / 2`,
`‖overlap t j a s s v‖ → +∞` as `v ↓ 0⁺`. -/
theorem tendsto_norm_self_overlap_atTop_of_re_lt_half (t : ExceptionalTime) (j : ℕ) (a : ℝ)
    {s : ℂ} (hs : s.re < 1 / 2) :
    Tendsto (fun v : ℝ => ‖AntipodalSpectrum.ComplementaryHalves.overlap t j a s s v‖)
      (𝓝[>] 0) atTop := by
  let C := clockRadix t j
  have hC_pos : 0 < ((tailRadix t j).val : ℝ) ^ s.re :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (tailRadix t j).pos) _
  have hpre : Tendsto (fun v : ℝ => ((tailRadix t j).val : ℝ) ^ s.re * (v * kernel C a v))
      (𝓝[>] 0) (𝓝 (((tailRadix t j).val : ℝ) ^ s.re)) := by
    simpa only [mul_one] using (kernel_mass C a).const_mul (((tailRadix t j).val : ℝ) ^ s.re)
  have hexp_pos : 0 < 1 - 2 * s.re := by linarith
  have hrpow_gt0 : Tendsto (fun v : ℝ => v ^ (1 - 2 * s.re)) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun v : ℝ => v ^ (1 - 2 * s.re)) 0 :=
        Real.continuousAt_rpow_const 0 (1 - 2 * s.re) (Or.inr hexp_pos.le)
      simpa only [Real.zero_rpow hexp_pos.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact Real.rpow_pos_of_pos hv _
  have hrpow_top : Tendsto (fun v : ℝ => v ^ (2 * s.re - 1)) (𝓝[>] 0) atTop := by
    refine (tendsto_inv_nhdsGT_zero.comp hrpow_gt0).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    dsimp only [Function.comp_apply]
    rw [← Real.rpow_neg (le_of_lt hv)]
    congr 1; ring
  refine (Tendsto.pos_mul_atTop hC_pos hpre hrpow_top).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (norm_self_overlap_eq t j a s hv).symm

/-- **Unconditional partition-vanishing conservation through height `84.5` and outside
`[3001/24000, 20999/24000]`:**
1. Every open-strip zero `s` of `continued` with `|Im s| ≤ 169 / 2` unconditionally satisfies
   `s.re = 1 / 2`, isometric `split s`, and `Tendsto (overlap t j a s s) (𝓝[>] 0) (𝓝 (C^s))`;
2. `continued` has no zeros with `0 < Re s < 3001 / 24000` or `20999 / 24000 < Re s`. -/
theorem joint_partition_zero_conserves_below_eightyFour_and_half
    (t : ExceptionalTime) (j : ℕ) (a : ℝ) :
    (∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| ≤ 169 / 2 → continued s = 0 →
      s.re = 1 / 2 ∧
      (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ∧
      Tendsto (AntipodalSpectrum.ComplementaryHalves.overlap t j a s s)
        (𝓝[>] 0) (𝓝 (((tailRadix t j).val : ℂ) ^ s))) ∧
    (∀ s : ℂ, 0 < s.re → (s.re < 3001 / 24000 ∨ 20999 / 24000 < s.re) → continued s ≠ 0) := by
  refine ⟨fun s h0 h1 him hc0 => ?_, fun s h0 hout hc0 => ?_⟩
  · have hζ : riemannZeta s = 0 := (positive_zero_iff ⟨s, h0⟩).mp hc0
    have hs1 : s ≠ 1 := fun he => h1.ne (by rw [he, Complex.one_re])
    have hxi : _root_.RHTower.xi s = 0 := (_root_.RHTower.xi_eq_zero_iff h0 hs1).mpr hζ
    have hre_half : s.re = 1 / 2 := by
      by_contra hne
      have hgt := VerifiedHeightRungs.lt_abs_im_of_rhVerifiedThrough
        VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_oneHundredSixtyNine_halves
        hxi h0 h1 hne
      linarith
    have hsd : s = 1 - conj s := (self_dual_iff s).mpr hre_half
    have hlim := ((thermal_limit_iff t j a s s (((tailRadix t j).val : ℂ) ^ s)).mpr ⟨hsd, rfl⟩).2
    exact ⟨hre_half, (split_isometric_iff s).mpr hre_half, hlim⟩
  · have hζ : riemannZeta s = 0 := (positive_zero_iff ⟨s, h0⟩).mp hc0
    have hmem := MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip h0 hζ
    rcases hout with hlt | hgt
    · linarith [hmem.1]
    · linarith [hmem.2]

/-- **Unified residual elimination theorem above Bohman height `169 / 2 = 84.5`:**
functional reflection collapses two-sided thermal conservation above `84.5` to a single one-sided
condition and unifies the operator-conservation and shell-cutoff branches on
`{1/2 < Re w ≤ 20999/24000 ∧ 169/2 < |Im w|}`. The following are unconditionally equivalent:
1. `RiemannHypothesis`;
2. **One-sided non-blow-up at left-strip partition zeros:** for every `s` with
   `3001 / 24000 ≤ Re s < 1 / 2`, `169 / 2 < |Im s|`, and `continued s = 0`,
   `∃ B : ℝ, ∃ᶠ v in 𝓝[>] 0, ‖overlap t j a s s v‖ ≤ B`;
3. **Non-dissipation at right-strip partition zeros:** for every `w` with
   `1 / 2 < Re w ≤ 20999 / 24000`, `169 / 2 < |Im w|`, and `continued w = 0`,
   `¬ Tendsto (overlap t j a w w) (𝓝[>] 0) (𝓝 0)`;
4. **Intrinsic Möbius shell margin:** for every `w` with `1 / 2 < Re w ≤ 20999 / 24000` and
   `169 / 2 < |Im w|`, there exist `M, K₀` (`1 ≤ K₀`, `M ≤ 4^K₀`) with
   `intrinsicDirichletZeroThreshold M moebiusReal K₀ w < ‖weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K₀ w‖`. -/
theorem rh_iff_unified_residual_elimination_above_eightyFour_and_half
    (t : ExceptionalTime) (j : ℕ) (a : ℝ) :
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 169 / 2 < |s.im| → continued s = 0 →
        ∃ B : ℝ, ∃ᶠ v : ℝ in 𝓝[>] 0,
          ‖AntipodalSpectrum.ComplementaryHalves.overlap t j a s s v‖ ≤ B) ∧
    (RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 169 / 2 < |w.im| → continued w = 0 →
        ¬ Tendsto (AntipodalSpectrum.ComplementaryHalves.overlap t j a w w) (𝓝[>] 0) (𝓝 0)) ∧
    (RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 169 / 2 < |w.im| →
        ∃ M K₀ : ℕ, 1 ≤ K₀ ∧ M ≤ 2 ^ (2 * K₀) ∧
          intrinsicDirichletZeroThreshold M moebiusReal K₀ w <
            ‖weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K₀ w‖) := by
  have h1 : RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 169 / 2 < |s.im| → continued s = 0 →
        ∃ B : ℝ, ∃ᶠ v : ℝ in 𝓝[>] 0,
          ‖AntipodalSpectrum.ComplementaryHalves.overlap t j a s s v‖ ≤ B := by
    constructor
    · intro hRH s hlo hhi _ hc0
      have hs0 : 0 < s.re := by linarith
      have hs1 : s.re < 1 := by linarith
      obtain ⟨L, hL_ne, hlim⟩ := (rh_iff_thermal_at_joint_zeros t j a).mp hRH ⟨s, hs0, hs1⟩ hc0
      have hre_eq := (((thermal_limit_iff t j a s s L).mp ⟨hL_ne, hlim⟩).1 |> (self_dual_iff s).mp)
      linarith
    · intro hnoblow
      rw [rh_iff_zetaFree_margin_above_eightyFour_and_half t j]
      intro w hw_lo hw_hi hw_im
      have hw0 : 0 < w.re := by linarith
      have hw1 : w.re < 1 := by linarith
      have hw_ne1 : w ≠ 1 := fun he => hw1.ne (by rw [he, Complex.one_re])
      rw [exists_zetaFree_margin_iff_zeta_ne_zero t j hw0 hw_ne1]
      intro hζw
      set s : ℂ := 1 - w
      have hs_re : s.re = 1 - w.re := by simp [s]
      have hs_im : |s.im| = |w.im| := by
        simp only [s, Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      have hs0 : 0 < s.re := by linarith
      have hs_lo : 3001 / 24000 ≤ s.re := by linarith
      have hs_hi : s.re < 1 / 2 := by linarith
      have hs_im_gt : 169 / 2 < |s.im| := by rwa [hs_im]
      have hζs : riemannZeta s = 0 :=
        _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζw hw0 hw1
      have hcs : continued s = 0 := (positive_zero_iff ⟨s, hs0⟩).mpr hζs
      obtain ⟨B, hfreq⟩ := hnoblow s hs_lo hs_hi hs_im_gt hcs
      have htop := tendsto_norm_self_overlap_atTop_of_re_lt_half t j a hs_hi
      have hev : ∀ᶠ v : ℝ in 𝓝[>] 0, B + 1 ≤
          ‖AntipodalSpectrum.ComplementaryHalves.overlap t j a s s v‖ :=
        htop.eventually (tendsto_atTop.mp tendsto_id (B + 1))
      obtain ⟨v, hv_le, hv_ge⟩ := (hfreq.and_eventually hev).exists
      linarith
  have h2 : RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 169 / 2 < |w.im| → continued w = 0 →
        ¬ Tendsto (AntipodalSpectrum.ComplementaryHalves.overlap t j a w w) (𝓝[>] 0) (𝓝 0) := by
    constructor
    · intro hRH w hlo hhi _ hcw
      have hw0 : 0 < w.re := by linarith
      have hw1 : w.re < 1 := by linarith
      obtain ⟨L, hL_ne, hlim⟩ := (rh_iff_thermal_at_joint_zeros t j a).mp hRH ⟨w, hw0, hw1⟩ hcw
      have hre_eq := (((thermal_limit_iff t j a w w L).mp ⟨hL_ne, hlim⟩).1 |> (self_dual_iff w).mp)
      linarith
    · intro hnodiss
      rw [rh_iff_zetaFree_margin_above_eightyFour_and_half t j]
      intro w hw_lo hw_hi hw_im
      have hw0 : 0 < w.re := by linarith
      have hw1 : w.re < 1 := by linarith
      have hw_ne1 : w ≠ 1 := fun he => hw1.ne (by rw [he, Complex.one_re])
      rw [exists_zetaFree_margin_iff_zeta_ne_zero t j hw0 hw_ne1]
      intro hζw
      exact hnodiss w hw_lo hw_hi hw_im ((positive_zero_iff ⟨w, hw0⟩).mpr hζw)
        (tendsto_self_overlap_zero_of_half_lt_re t j a hw_lo)
  exact ⟨h1, h2, rh_iff_intrinsic_moebius_margin_above_eightyFour_and_half.1⟩

#print axioms sq_commuting_positive_conserving_eq_critical
#print axioms commuting_positive_conserving_iff_eq_critical
#print axioms noncanonical_positive_conserving_breaks_shell_diagonal
#print axioms hsNormSq_critical_sq_sub_sq_le_fourth_trace_defect
#print axioms norm_critical_sq_sub_sq_le_sqrt_fourth_trace_defect
#print axioms norm_omitted_eq_one_of_ne_critical
#print axioms tiltedShellPropagator_properties
#print axioms tendsto_tiltedShell_stability_ratio_one
#print axioms norm_self_overlap_eq
#print axioms tendsto_self_overlap_zero_of_half_lt_re
#print axioms tendsto_norm_self_overlap_atTop_of_re_lt_half
#print axioms joint_partition_zero_conserves_below_eightyFour_and_half
#print axioms rh_iff_unified_residual_elimination_above_eightyFour_and_half

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas