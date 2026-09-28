import GaloisForLFunctions.RHTower.CCMPrimePolePolynomialBoundary
import GaloisForLFunctions.RHTower.SoninEulerCornerNoncompact

/-!
# Weyl spectra under compact perturbation and isometric compression

The Weyl spectrum of a bounded operator `T` on a Hilbert space is the set of `c` admitting a
**Weyl sequence**: unit vectors `fₙ`, weakly null, with `‖T fₙ - c fₙ‖ → 0`.  For self-adjoint
operators this is the essential spectrum.  This module proves the transfer rules used for operator
models:

* compact perturbations do not change the Weyl spectrum;
* a Weyl value bounds the essential norm from below;
* Weyl values of an operator with nonnegative (resp. bounded above) numerical range are
  nonnegative (resp. bounded above);
* for an isometry `U` and an operator `A` supported on its range (`A = PA = AP`, `P = UU*`), the
  compression `M = U* A U` has the same nonzero Weyl values as `A`.  The last point uses the
  orthogonal splitting `(A - c) g = (A - c) P g - c (1 - P) g`: both pieces must vanish, so a Weyl
  sequence of `A` concentrates on the range of `U`.

Finally, a sequence of unit pairs with `|⟪fₙ, T gₙ⟫| → c`, `gₙ` weakly null, bounds the essential
norm of `T` from below by `c`.
-/

open Filter Topology

noncomputable section
set_option autoImplicit false

namespace RHTower

variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

/-- The **Weyl spectrum**: values `c` with a weakly null unit sequence `fₙ`,
`‖T fₙ - c fₙ‖ → 0`. -/
def weylEssentialSpectrum (T : H →L[ℂ] H) : Set ℂ :=
  {c | ∃ f : ℕ → H, (∀ n, ‖f n‖ = 1) ∧
    (∀ ℓ : H →L[ℂ] ℂ, Tendsto (fun n => ℓ (f n)) atTop (𝓝 0)) ∧
    Tendsto (fun n => ‖T (f n) - c • f n‖) atTop (𝓝 0)}

/-- An orthonormal Weyl sequence certifies a Weyl value. -/
theorem mem_weylEssentialSpectrum_of_orthonormal [CompleteSpace H] {T : H →L[ℂ] H} {c : ℂ}
    {f : ℕ → H} (hf : Orthonormal ℂ f) (hT : Tendsto (fun n => ‖T (f n) - c • f n‖) atTop (𝓝 0)) :
    c ∈ weylEssentialSpectrum T :=
  ⟨f, hf.1, Orthonormal.weakly_tendsto_zero hf, hT⟩

/-- **Compact perturbations preserve Weyl values.** -/
theorem weylEssentialSpectrum_mono_of_isCompactOperator {S T : H →L[ℂ] H}
    (hK : IsCompactOperator (T - S)) {c : ℂ} (hc : c ∈ weylEssentialSpectrum S) :
    c ∈ weylEssentialSpectrum T := by
  obtain ⟨f, hf1, hfw, hS⟩ := hc
  refine ⟨f, hf1, hfw, ?_⟩
  have hK0 := IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null (T - S) hK f 1
    (fun n => (hf1 n).le) hfw
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hS.add hK0)
  calc ‖T (f n) - c • f n‖ = ‖(S (f n) - c • f n) + (T - S) (f n)‖ := by
        congr 1; rw [_root_.sub_apply]; abel
    _ ≤ ‖S (f n) - c • f n‖ + ‖(T - S) (f n)‖ := norm_add_le _ _

theorem weylEssentialSpectrum_eq_of_isCompactOperator {S T : H →L[ℂ] H}
    (hK : IsCompactOperator (T - S)) : weylEssentialSpectrum T = weylEssentialSpectrum S := by
  have hK' : IsCompactOperator (S - T) := by
    have h : ⇑(S - T) = -⇑(T - S) := by ext x; simp
    rw [h]; exact hK.neg
  exact Set.Subset.antisymm (fun c hc => weylEssentialSpectrum_mono_of_isCompactOperator hK' hc)
    fun c hc => weylEssentialSpectrum_mono_of_isCompactOperator hK hc

/-- A Weyl value bounds the essential norm from below. -/
theorem norm_le_essentialNorm_of_mem_weylEssentialSpectrum [CompleteSpace H] {T : H →L[ℂ] H}
    {c : ℂ} (hc : c ∈ weylEssentialSpectrum T) : ‖c‖ ≤ essentialNorm T := by
  obtain ⟨f, hf1, hfw, hT⟩ := hc
  exact norm_le_essentialNorm_of_weaklyNull_approx_eigenvector T f c hf1 hfw hT

/-- Along a Weyl sequence the numerical values converge to the Weyl value. -/
theorem tendsto_inner_of_weyl {T : H →L[ℂ] H} {c : ℂ} {f : ℕ → H} (hf1 : ∀ n, ‖f n‖ = 1)
    (hT : Tendsto (fun n => ‖T (f n) - c • f n‖) atTop (𝓝 0)) :
    Tendsto (fun n => inner ℂ (f n) (T (f n))) atTop (𝓝 c) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hT
  have hself : inner ℂ (f n) (f n) = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hf1 n]; norm_num
  calc ‖inner ℂ (f n) (T (f n)) - c‖ = ‖inner ℂ (f n) (T (f n) - c • f n)‖ := by
        rw [inner_sub_right, inner_smul_right, hself, mul_one]
    _ ≤ ‖f n‖ * ‖T (f n) - c • f n‖ := norm_inner_le_norm _ _
    _ = ‖T (f n) - c • f n‖ := by rw [hf1 n, one_mul]

/-- Weyl values of an operator with nonnegative numerical range are nonnegative. -/
theorem re_nonneg_of_mem_weylEssentialSpectrum {T : H →L[ℂ] H}
    (hpos : ∀ x, 0 ≤ (inner ℂ x (T x)).re) {c : ℂ} (hc : c ∈ weylEssentialSpectrum T) :
    0 ≤ c.re := by
  obtain ⟨f, hf1, -, hT⟩ := hc
  have h := (Complex.continuous_re.tendsto c).comp (tendsto_inner_of_weyl hf1 hT)
  exact ge_of_tendsto h (Eventually.of_forall fun n => hpos (f n))

/-- Weyl values of an operator with numerical range bounded by `M` have real part at most `M`. -/
theorem re_le_of_mem_weylEssentialSpectrum {T : H →L[ℂ] H} {M : ℝ}
    (hM : ∀ x, (inner ℂ x (T x)).re ≤ M * ‖x‖ ^ 2) {c : ℂ} (hc : c ∈ weylEssentialSpectrum T) :
    c.re ≤ M := by
  obtain ⟨f, hf1, -, hT⟩ := hc
  have h := (Complex.continuous_re.tendsto c).comp (tendsto_inner_of_weyl hf1 hT)
  exact le_of_tendsto h (Eventually.of_forall fun n => by
    simpa [Function.comp_apply, hf1 n] using hM (f n))

/-- Weyl values of a self-adjoint operator are real. -/
theorem im_eq_zero_of_mem_weylEssentialSpectrum [CompleteSpace H] {T : H →L[ℂ] H}
    (hT : IsSelfAdjoint T) {c : ℂ}
    (hc : c ∈ weylEssentialSpectrum T) : c.im = 0 := by
  obtain ⟨f, hf1, -, hTc⟩ := hc
  have h := (Complex.continuous_im.tendsto c).comp (tendsto_inner_of_weyl hf1 hTc)
  refine tendsto_nhds_unique h (tendsto_const_nhds.congr fun n => ?_)
  have hsym : inner ℂ (f n) (T (f n)) = (starRingEnd ℂ) (inner ℂ (f n) (T (f n))) := by
    rw [inner_conj_symm]
    exact (hT.isSymmetric (f n) (f n)).symm
  have := congrArg Complex.im hsym
  simp only [Complex.conj_im] at this
  simp only [Function.comp_apply]
  linarith

/-! ### Isometric compression -/

section Compression

variable [CompleteSpace H] [CompleteSpace L]

/-- A bounded operator with `U* U = 1` is an isometry. -/
theorem norm_apply_of_adjoint_comp_eq_id {U : H →L[ℂ] L}
    (hU : U.adjoint ∘L U = ContinuousLinearMap.id ℂ H) (x : H) : ‖U x‖ = ‖x‖ := by
  have h : inner ℂ (U x) (U x) = inner ℂ x x := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, hU,
      ContinuousLinearMap.id_apply]
  have h2 := congrArg Complex.re h
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
  norm_cast at h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- Weyl values of the compression `U* A U` are Weyl values of `A`, when `A` maps into the range
of the isometry `U`. -/
theorem mem_weylEssentialSpectrum_of_compression {U : H →L[ℂ] L} {A : L →L[ℂ] L}
    (hU : U.adjoint ∘L U = ContinuousLinearMap.id ℂ H)
    (hPA : U ∘L U.adjoint ∘L A = A) {c : ℂ}
    (hc : c ∈ weylEssentialSpectrum (U.adjoint ∘L A ∘L U)) : c ∈ weylEssentialSpectrum A := by
  obtain ⟨f, hf1, hfw, hT⟩ := hc
  have hiso := norm_apply_of_adjoint_comp_eq_id hU
  refine ⟨fun n => U (f n), fun n => by rw [hiso, hf1], fun ℓ => ?_, ?_⟩
  · simpa using hfw (ℓ ∘L U)
  · refine hT.congr fun n => ?_
    rw [← hiso]
    congr 1
    conv_rhs => rw [← hPA]
    simp [map_sub, map_smul]

/-- **Nonzero Weyl values descend to the compression.**  If `U` is an isometry and `A` is supported
on its range (`P A = A = A P`, `P = UU*`), every nonzero Weyl value of `A` is a Weyl value of
`U* A U`. -/
theorem mem_weylEssentialSpectrum_compression {U : H →L[ℂ] L} {A : L →L[ℂ] L}
    (hU : U.adjoint ∘L U = ContinuousLinearMap.id ℂ H)
    (hPA : U ∘L U.adjoint ∘L A = A) (hAP : A ∘L U ∘L U.adjoint = A) {c : ℂ} (hc0 : c ≠ 0)
    (hc : c ∈ weylEssentialSpectrum A) :
    c ∈ weylEssentialSpectrum (U.adjoint ∘L A ∘L U) := by
  obtain ⟨g, hg1, hgw, hA⟩ := hc
  set P : L →L[ℂ] L := U ∘L U.adjoint with hPdef
  have hiso := norm_apply_of_adjoint_comp_eq_id hU
  have hUadj : ∀ x, U (U.adjoint (U x)) = U x := fun x => by
    rw [← ContinuousLinearMap.comp_apply U.adjoint U, hU, ContinuousLinearMap.id_apply]
  -- orthogonality of the range of `P` and its complement
  have horth : ∀ x y : L, inner ℂ (P x) (y - P y) = 0 := by
    intro x y
    simp only [hPdef, ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_right, map_sub, ← ContinuousLinearMap.comp_apply
      U.adjoint U, hU, ContinuousLinearMap.id_apply, sub_self, inner_zero_right]
  have hP2 : ∀ x, P (P x) = P x := fun x => by
    simp only [hPdef, ContinuousLinearMap.comp_apply, hUadj]
  set e : ℕ → L := fun n => A (P (g n)) - c • P (g n) with hedef
  have hsplit : ∀ n, A (g n) - c • g n = P (e n) - c • (g n - P (g n)) := by
    intro n
    have h1 : A (g n) = A (P (g n)) :=
      (congrArg (fun T : L →L[ℂ] L => T (g n)) hAP).symm
    have h2 : P (A (P (g n))) = A (P (g n)) :=
      congrArg (fun T : L →L[ℂ] L => T (P (g n))) hPA
    simp only [hedef, map_sub, map_smul, hP2, h2, h1, smul_sub]
    abel
  have hpyth : ∀ n, ‖A (g n) - c • g n‖ ^ 2 =
      ‖P (e n)‖ ^ 2 + ‖c‖ ^ 2 * ‖g n - P (g n)‖ ^ 2 := by
    intro n
    rw [hsplit n, @norm_sub_sq ℂ, norm_smul, mul_pow, inner_smul_right, horth, mul_zero]
    simp
  have hsq : Tendsto (fun n => ‖A (g n) - c • g n‖ ^ 2) atTop (𝓝 0) := by
    simpa using hA.pow 2
  -- both orthogonal pieces vanish
  have hcomp : Tendsto (fun n => ‖g n - P (g n)‖) atTop (𝓝 0) := by
    have hc2 : 0 < ‖c‖ ^ 2 := by positivity
    have hdiv : Tendsto (fun n => ‖A (g n) - c • g n‖ ^ 2 / ‖c‖ ^ 2) atTop (𝓝 0) := by
      simpa using hsq.div_const (‖c‖ ^ 2)
    have h : Tendsto (fun n => ‖g n - P (g n)‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => by positivity) (fun n => ?_) hdiv
      rw [le_div_iff₀ hc2, hpyth n]
      nlinarith [sq_nonneg ‖P (e n)‖]
    have := h.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have hmain : Tendsto (fun n => ‖P (e n)‖) atTop (𝓝 0) := by
    have h : Tendsto (fun n => ‖P (e n)‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => by positivity) (fun n => ?_) hsq
      rw [hpyth n]
      nlinarith [sq_nonneg ‖g n - P (g n)‖, sq_nonneg ‖c‖]
    have := h.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  -- the compressed vectors have norm tending to one
  have hnormU : Tendsto (fun n => ‖U.adjoint (g n)‖) atTop (𝓝 1) := by
    have hPn : ∀ n, ‖U.adjoint (g n)‖ = ‖P (g n)‖ := fun n => by
      simp only [hPdef, ContinuousLinearMap.comp_apply, hiso]
    have hlow : ∀ n, 1 - ‖g n - P (g n)‖ ≤ ‖U.adjoint (g n)‖ := fun n => by
      rw [hPn, ← hg1 n]
      have := norm_sub_norm_le (g n) (g n - P (g n))
      rw [sub_sub_cancel] at this
      linarith
    have hup : ∀ n, ‖U.adjoint (g n)‖ ≤ 1 + ‖g n - P (g n)‖ := fun n => by
      rw [hPn, ← hg1 n]
      have := norm_sub_norm_le (P (g n)) (P (g n) - g n)
      rw [sub_sub_cancel, norm_sub_rev] at this
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => 1 - ‖g n - P (g n)‖)
      (h := fun n => 1 + ‖g n - P (g n)‖) ?_ ?_ hlow hup
    · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hcomp
    · simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hcomp
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hnormU.eventually (lt_mem_nhds (by norm_num :
    (1 / 2 : ℝ) < 1)))
  set u : ℕ → H := fun n => U.adjoint (g (n + N)) with hudef
  have hupos : ∀ n, 1 / 2 < ‖u n‖ := fun n => hN (n + N) (Nat.le_add_left _ _)
  have hune : ∀ n, u n ≠ 0 := fun n h => by
    have := hupos n; rw [h, norm_zero] at this; linarith
  refine ⟨fun n => ((‖u n‖ : ℂ))⁻¹ • u n, fun n => ?_, fun ℓ => ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr
      (hune n))]
  · have hw : Tendsto (fun n => ℓ (u n)) atTop (𝓝 0) := by
      have := (hgw (ℓ ∘L U.adjoint)).comp (tendsto_add_atTop_nat N)
      simpa [hudef, Function.comp_def] using this
    have hinv : Tendsto (fun n => ((‖u n‖ : ℂ))⁻¹) atTop (𝓝 1) := by
      have h1 : Tendsto (fun n => ‖u n‖) atTop (𝓝 1) := hnormU.comp (tendsto_add_atTop_nat N)
      have h2 := (Complex.continuous_ofReal.tendsto 1).comp h1
      simpa using h2.inv₀ (by norm_num)
    simpa [map_smul] using hinv.mul hw
  · have hbound : ∀ n, ‖(U.adjoint ∘L A ∘L U) (((‖u n‖ : ℂ))⁻¹ • u n) -
        c • (((‖u n‖ : ℂ))⁻¹ • u n)‖ ≤ 2 * ‖P (e (n + N))‖ := by
      intro n
      have hkey : ‖(U.adjoint ∘L A ∘L U) (u n) - c • u n‖ = ‖P (e (n + N))‖ := by
        rw [← hiso]
        congr 1
        simp only [hudef, hedef, hPdef, ContinuousLinearMap.comp_apply, map_sub, map_smul, hUadj]
      rw [map_smul, smul_comm c, ← smul_sub, norm_smul, norm_inv, Complex.norm_real,
        norm_norm, hkey]
      have hu := hupos n
      rw [inv_mul_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (P (e (n + N)))]
    refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
    simpa using (hmain.comp (tendsto_add_atTop_nat N)).const_mul 2

end Compression

/-! ### Pairing lower bound for the essential norm -/

/-- If unit pairs `fₙ, gₙ` with `gₙ` weakly null satisfy `bₙ ≤ |⟪fₙ, T gₙ⟫|` eventually and
`bₙ → c`, then `c ≤ ‖T‖_ess`. -/
theorem le_essentialNorm_of_pairing {T : H →L[ℂ] H} {f g : ℕ → H} {b : ℕ → ℝ} {c : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (hgw : ∀ ℓ : H →L[ℂ] ℂ, Tendsto (fun n => ℓ (g n)) atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, b n ≤ ‖inner ℂ (f n) (T (g n))‖) (hbc : Tendsto b atTop (𝓝 c)) :
    c ≤ essentialNorm T := by
  refine le_essentialNorm T c fun K hK => ?_
  have hK0 := IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null K hK g 1 hg hgw
  have hle : ∀ᶠ n in atTop, b n ≤ ‖T - K‖ + ‖K (g n)‖ := by
    filter_upwards [hb] with n hn
    calc b n ≤ ‖inner ℂ (f n) (T (g n))‖ := hn
      _ = ‖inner ℂ (f n) ((T - K) (g n)) + inner ℂ (f n) (K (g n))‖ := by
          rw [← inner_add_right, _root_.sub_apply, sub_add_cancel]
      _ ≤ ‖f n‖ * ‖(T - K) (g n)‖ + ‖f n‖ * ‖K (g n)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
      _ ≤ 1 * (‖T - K‖ * 1) + 1 * ‖K (g n)‖ := by
          gcongr
          · exact hf n
          · exact ((T - K).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hg n) (norm_nonneg _))
          · exact hf n
      _ = ‖T - K‖ + ‖K (g n)‖ := by ring
  have := le_of_tendsto_of_tendsto hbc (tendsto_const_nhds.add hK0) hle
  simpa using this

/-! ### Unitary invariance -/

theorem mem_weylEssentialSpectrum_unitary_conj [CompleteSpace H] [CompleteSpace L]
    (u : H ≃ₗᵢ[ℂ] L) {T : H →L[ℂ] H} {c : ℂ} (hc : c ∈ weylEssentialSpectrum T) :
    c ∈ weylEssentialSpectrum ((u.toContinuousLinearEquiv : H →L[ℂ] L) ∘L T ∘L
      (u.symm.toContinuousLinearEquiv : L →L[ℂ] H)) := by
  obtain ⟨f, hf1, hfw, hT⟩ := hc
  refine ⟨fun n => u (f n), fun n => by rw [u.norm_map, hf1], fun ℓ => ?_, ?_⟩
  · simpa using hfw (ℓ ∘L (u.toContinuousLinearEquiv : H →L[ℂ] L))
  · refine hT.congr fun n => ?_
    rw [← u.norm_map]
    simp

end RHTower
