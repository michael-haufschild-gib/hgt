import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLinearWindow
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.HTGeometry.PolynomialCoeffMassLagrange

/-!
# The height horizon of the fixed-rank heat Hankel ladder

For a heat time `a > 0` let `Δ_N(a) = det (M_{i+j}(a))_{i,j<N}` be the leading Hankel determinants of
the zero heat moments `M_n(a) = Σ_q w_q^n e^{-a w_q}`, `w_q = z_q²`.  RH holds iff every `Δ_N(a)` is
positive, and without RH some `Δ_N` vanishes.

**Theorem** (`exists_height_heatMomentDet_pos`).  For every rank `N` there is a height `H` such
that `Δ_N(a) > 0` at every heat time `a > 0` as soon as every off-line zero `ρ = ½ + δ + iγ`,
`δ ≠ 0`, has `|γ| > H`.

A fixed rank of the ladder, read at all heat times at once, therefore sees off-line zeros only
below a finite height, and the same height works for all ranks `≤ N`
(`exists_height_forall_le_heatMomentDet_pos`).  Contrapositively, a nonpositive value of `Δ_N`
anywhere on the heat axis locates an off-line zero of height at most `H(N)`
(`exists_offLine_height_le_of_heatMomentDet_nonpos`).

Proof.  Small times `a (d + 1) ≤ κ` are the unconditional linear window.  For larger times take
`d + 1` real zeros `t_0 < ⋯ < t_d` from Hardy's theorem.  Their squares are distinct real heat
frequencies, and Lagrange interpolation bounds the coefficient mass of a polynomial of degree `≤ d`
by its values there, so these frequencies contribute at least `e^{-aΛ} Σ_i |P(t_i²)|²`,
`Λ = t_d²`, which controls `coeffMass(P)²`.  Every other real frequency contributes a nonnegative
amount.  An off-line frequency of height `> H` has `Re w > Λ`, so its contribution is at most
`coeffMass(P)² e^{-aΛ} e^{a₀Λ} f(w)` with `f(w) = (1 + |w|)^{2d} e^{-a₀ Re w}` summable, and all
off-line frequencies lie outside a finite set that carries all but a small part of `Σ f`.
-/

open Complex Polynomial Matrix Filter Topology
open GaloisForLFunctions.HTGeometry (leadingMatrix coeffMass coeffMass_nonneg coeffMass_le_of_nodes
  coeffMass_eq_sum_range)

namespace RHTower

noncomputable section

/-! ## An increasing sequence of real zeros -/

/-- The `n`-th real zero obtained by iterating Hardy's theorem from `0`. -/
def hardyRealZero : ℕ → ℝ
  | 0 => Classical.choose (exists_Xi_zero_gt 0)
  | n + 1 => Classical.choose (exists_Xi_zero_gt (hardyRealZero n))

theorem Xi_hardyRealZero (n : ℕ) : Xi (hardyRealZero n) = 0 := by
  cases n with
  | zero => exact (Classical.choose_spec (exists_Xi_zero_gt 0)).2
  | succ k => exact (Classical.choose_spec (exists_Xi_zero_gt (hardyRealZero k))).2

theorem hardyRealZero_zero_pos : 0 < hardyRealZero 0 :=
  (Classical.choose_spec (exists_Xi_zero_gt 0)).1

theorem hardyRealZero_lt_succ (n : ℕ) : hardyRealZero n < hardyRealZero (n + 1) :=
  (Classical.choose_spec (exists_Xi_zero_gt (hardyRealZero n))).1

theorem strictMono_hardyRealZero : StrictMono hardyRealZero :=
  strictMono_nat_of_lt_succ hardyRealZero_lt_succ

theorem hardyRealZero_pos (n : ℕ) : 0 < hardyRealZero n :=
  hardyRealZero_zero_pos.trans_le (strictMono_hardyRealZero.monotone (Nat.zero_le n))

theorem exists_xiZeroCopy_eq_hardyRealZero (n : ℕ) :
    ∃ q : XiZeroCopy, xiSpectralPoint q = (hardyRealZero n : ℂ) :=
  (XiC_eq_zero_iff_exists_xiZeroCopy _).1 (by rw [XiC_ofReal, Xi_hardyRealZero, ofReal_zero])

/-- A zero copy sitting at the `n`-th real zero. -/
def hardyCopy (n : ℕ) : XiZeroCopy := Classical.choose (exists_xiZeroCopy_eq_hardyRealZero n)

theorem xiSpectralPoint_hardyCopy (n : ℕ) :
    xiSpectralPoint (hardyCopy n) = (hardyRealZero n : ℂ) :=
  Classical.choose_spec (exists_xiZeroCopy_eq_hardyRealZero n)

theorem xiHeatFrequency_hardyCopy (n : ℕ) :
    xiHeatFrequency (hardyCopy n) = ((hardyRealZero n ^ 2 : ℝ) : ℂ) := by
  rw [xiHeatFrequency, xiSpectralPoint_hardyCopy]
  push_cast
  ring

theorem hardyCopy_injective : Function.Injective hardyCopy := fun m n h => by
  have := congrArg xiSpectralPoint h
  rw [xiSpectralPoint_hardyCopy, xiSpectralPoint_hardyCopy, ofReal_inj] at this
  exact strictMono_hardyRealZero.injective this

/-! ## Interpolation at the squared real zeros -/

theorem coeffMass_pos {P : ℂ[X]} (hP : P ≠ 0) : 0 < coeffMass P := by
  rw [coeffMass_eq_sum_range P (Nat.lt_succ_self P.natDegree)]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun k _ => norm_nonneg (P.coeff k))
    (Finset.self_mem_range_succ P.natDegree))
  rw [norm_pos_iff, ← leadingCoeff]
  exact leadingCoeff_ne_zero.2 hP

/-- A polynomial of degree `≤ d` is controlled by its values at the squares of the first `d + 1`
real zeros. -/
theorem exists_coeffMass_le_hardyNodes (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℂ[X], P.natDegree ≤ d →
      coeffMass P ≤ C * ∑ i : Fin (d + 1), ‖P.eval (xiHeatFrequency (hardyCopy i))‖ := by
  set t : Fin (d + 1) → ℂ := fun i => xiHeatFrequency (hardyCopy i) with ht
  have hnorm : ∀ i : Fin (d + 1), ‖t i‖ = hardyRealZero i ^ 2 := fun i => by
    show ‖xiHeatFrequency (hardyCopy i)‖ = _
    rw [xiHeatFrequency_hardyCopy, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
  have hR : ∀ i : Fin (d + 1), ‖t i‖ ≤ hardyRealZero d ^ 2 := fun i => by
    rw [hnorm]
    have h0 := (hardyRealZero_pos i).le
    have h1 := strictMono_hardyRealZero.monotone (Nat.lt_succ_iff.1 i.2)
    nlinarith
  have hpos : ∀ i j : Fin (d + 1), i ≠ j → 0 < ‖t i - t j‖ := fun i j hij => by
    rw [norm_pos_iff, sub_ne_zero, ht]
    intro heq
    simp only [xiHeatFrequency_hardyCopy, ofReal_inj] at heq
    have := (pow_left_inj₀ (hardyRealZero_pos i).le (hardyRealZero_pos j).le two_ne_zero).1 heq
    exact hij (Fin.ext (strictMono_hardyRealZero.injective this))
  obtain ⟨h, hh, hsep⟩ : ∃ h : ℝ, 0 < h ∧ ∀ i j : Fin (d + 1), i ≠ j → h ≤ ‖t i - t j‖ := by
    rcases isEmpty_or_nonempty {p : Fin (d + 1) × Fin (d + 1) // p.1 ≠ p.2} with hE | hN
    · exact ⟨1, one_pos, fun i j hij => (hE.false ⟨(i, j), hij⟩).elim⟩
    · obtain ⟨p, hp⟩ := Finite.exists_min
        (fun p : {p : Fin (d + 1) × Fin (d + 1) // p.1 ≠ p.2} => ‖t p.1.1 - t p.1.2‖)
      exact ⟨_, hpos _ _ p.2, fun i j hij => hp ⟨(i, j), hij⟩⟩
  exact ⟨((1 + hardyRealZero d ^ 2) / h) ^ d, by positivity,
    fun P hP => coeffMass_le_of_nodes t hh hR hsep P hP⟩

/-! ## Domination at large heat times -/

/-- **Fixed-degree height horizon.**  For every degree `d` there is a height `H` such that, when
every off-line zero has height `> H`, the heat Hankel form is positive on every nonzero polynomial
of degree `≤ d` at every heat time `a > 0`. -/
theorem exists_height_heatHankel_re_pos (d : ℕ) :
    ∃ H : ℝ, (∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → H < |(xiSpectralPoint q).re|) →
      ∀ a : ℝ, 0 < a → ∀ P : ℂ[X], P ≠ 0 → P.natDegree ≤ d → 0 < (heatHankel a P P).re := by
  obtain ⟨C, hC0, hC⟩ := exists_coeffMass_le_hardyNodes d
  set κ := routeUCompletedPrimeGammaAperture with hκ
  set a₀ : ℝ := κ / (d + 1) with ha₀
  have ha₀pos : 0 < a₀ := div_pos routeUCompletedPrimeGammaAperture_pos (by positivity)
  set Λ : ℝ := hardyRealZero d ^ 2 with hΛ
  set K : ℝ := C ^ 2 * (d + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  set f : XiZeroCopy → ℝ := fun q =>
    (1 + ‖xiHeatFrequency q‖) ^ (2 * d) * Real.exp (-(a₀ * (xiHeatFrequency q).re)) with hf
  have hfs : Summable f := summable_one_add_norm_pow_mul_exp ha₀pos (2 * d)
  have hf0 : ∀ q, 0 ≤ f q := fun q => by positivity
  set ε : ℝ := 1 / (2 * (K + 1) * Real.exp (a₀ * Λ)) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨F, hF⟩ : ∃ F : Finset XiZeroCopy,
      ∑' q, ((↑F : Set XiZeroCopy)ᶜ.indicator f q) < ε := by
    obtain ⟨F, hF⟩ := ((tendsto_tsum_compl_atTop_zero f).eventually (gt_mem_nhds hεpos)).exists
    exact ⟨F, by rw [← tsum_subtype]; exact hF⟩
  refine ⟨Real.sqrt (Λ + 1) + ∑ q ∈ F, |(xiSpectralPoint q).re|,
    fun hhigh a ha P hP hPd => ?_⟩
  rcases le_or_gt (a * (d + 1)) κ with hwin | hwin
  · refine heatHankel_re_pos_of_window ha hP (le_trans ?_ hwin)
    have : (P.natDegree : ℝ) ≤ d := by exact_mod_cast hPd
    nlinarith
  have haa : a₀ < a := by rw [ha₀, div_lt_iff₀ (by positivity)]; exact hwin
  set H := Real.sqrt (Λ + 1) + ∑ q ∈ F, |(xiSpectralPoint q).re| with hH
  have hsqrt := Real.sqrt_nonneg (Λ + 1)
  have hsum0 : 0 ≤ ∑ q ∈ F, |(xiSpectralPoint q).re| :=
    Finset.sum_nonneg fun q _ => abs_nonneg _
  -- off-line copies lie outside `F` and above `Λ`
  have hoffF : ∀ q, (xiSpectralPoint q).im ≠ 0 → q ∉ F := fun q hq hqF => by
    have := Finset.single_le_sum (fun q _ => abs_nonneg ((xiSpectralPoint q).re)) hqF
    linarith [hhigh q hq]
  have hoffΛ : ∀ q, (xiSpectralPoint q).im ≠ 0 → Λ ≤ (xiHeatFrequency q).re := fun q hq => by
    have h1 := hhigh q hq
    have hHge : Real.sqrt (Λ + 1) ≤ |(xiSpectralPoint q).re| := by linarith
    have hΛ0 : 0 ≤ Λ + 1 := by positivity
    have h2 : Λ + 1 ≤ (xiSpectralPoint q).re ^ 2 := by
      have := mul_self_le_mul_self hsqrt hHge
      rw [Real.mul_self_sqrt hΛ0, abs_mul_abs_self] at this
      nlinarith
    have h3 := xiSpectralPoint_im_sq_lt_quarter q
    rw [xiHeatFrequency_re]
    linarith
  set M : ℝ := coeffMass P ^ 2 * Real.exp (-(a * Λ)) * Real.exp (a₀ * Λ) with hM
  have hM0 : 0 ≤ M := by positivity
  set O : Set XiZeroCopy := {q | (xiSpectralPoint q).im ≠ 0} with hO
  set T : XiZeroCopy → ℝ := fun q => (heatHankelTermAt a P P (xiHeatFrequency q)).re with hT
  have hTs : Summable T := (Complex.hasSum_re (summable_heatHankelTermAt ha P P).hasSum).summable
  have hBs : Summable (O.indicator f) := hfs.indicator O
  -- pointwise: every term is at least `-M f` on the off-line set and `≥ 0` elsewhere
  have hpt : ∀ q, 0 ≤ T q + M * O.indicator f q := fun q => by
    by_cases hq : (xiSpectralPoint q).im = 0
    · have hw : (xiHeatFrequency q).im = 0 := by rw [xiHeatFrequency_im, hq, mul_zero]
      have hqO : q ∉ O := fun h => h hq
      rw [Set.indicator_of_notMem hqO, mul_zero, add_zero, hT]
      dsimp only
      rw [re_heatHankelTermAt_of_im_eq_zero a P hw]
      positivity
    · have hqO : q ∈ O := hq
      rw [Set.indicator_of_mem hqO]
      have hnorm := norm_heatHankelTermAt_le a P P q
      have hre : -‖heatHankelTermAt a P P (xiHeatFrequency q)‖ ≤ T q := by
        rw [hT]; exact neg_le_of_abs_le (Complex.abs_re_le_norm _)
      have hbase : 1 ≤ 1 + ‖xiHeatFrequency q‖ := by linarith [norm_nonneg (xiHeatFrequency q)]
      have hpow : (1 + ‖xiHeatFrequency q‖) ^ (P.natDegree + P.natDegree) ≤
          (1 + ‖xiHeatFrequency q‖) ^ (2 * d) := pow_le_pow_right₀ hbase (by omega)
      have hexp : Real.exp (-(a * (xiHeatFrequency q).re)) ≤
          Real.exp (-(a * Λ)) * Real.exp (a₀ * Λ) *
            Real.exp (-(a₀ * (xiHeatFrequency q).re)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have := hoffΛ q hq
        nlinarith
      have hmass : polyMass P = coeffMass P := rfl
      rw [hmass] at hnorm
      have hc := coeffMass_nonneg P
      have hle : ‖heatHankelTermAt a P P (xiHeatFrequency q)‖ ≤ M * f q := by
        refine hnorm.trans ?_
        rw [hM, hf]
        dsimp only
        calc coeffMass P * coeffMass P * ((1 + ‖xiHeatFrequency q‖) ^ (P.natDegree + P.natDegree) *
              Real.exp (-(a * (xiHeatFrequency q).re)))
            ≤ coeffMass P * coeffMass P * ((1 + ‖xiHeatFrequency q‖) ^ (2 * d) *
              (Real.exp (-(a * Λ)) * Real.exp (a₀ * Λ) *
                Real.exp (-(a₀ * (xiHeatFrequency q).re)))) := by gcongr
          _ = _ := by ring
      linarith
  -- the real nodes
  set S : Finset XiZeroCopy := Finset.univ.image fun i : Fin (d + 1) => hardyCopy i with hS
  have hlow := (hTs.add (hBs.mul_left M)).sum_le_tsum S fun q _ => hpt q
  rw [Summable.tsum_add hTs (hBs.mul_left M), tsum_mul_left] at hlow
  have hinj : Set.InjOn (fun i : Fin (d + 1) => hardyCopy i) ↑(Finset.univ : Finset (Fin (d + 1))) :=
    fun i _ j _ hij => Fin.ext (hardyCopy_injective hij)
  rw [hS, Finset.sum_image hinj] at hlow
  have hnode : ∀ i : Fin (d + 1),
      Real.exp (-(a * Λ)) * ‖P.eval (xiHeatFrequency (hardyCopy i))‖ ^ 2 ≤
        T (hardyCopy i) + M * O.indicator f (hardyCopy i) := fun i => by
    have him : (xiSpectralPoint (hardyCopy i)).im = 0 := by
      rw [xiSpectralPoint_hardyCopy, ofReal_im]
    have hw : (xiHeatFrequency (hardyCopy i)).im = 0 := by
      rw [xiHeatFrequency_im, him, mul_zero]
    have hqO : hardyCopy i ∉ O := fun h => h him
    rw [Set.indicator_of_notMem hqO, mul_zero, add_zero, hT]
    dsimp only
    rw [re_heatHankelTermAt_of_im_eq_zero a P hw]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
    have hre : (xiHeatFrequency (hardyCopy i)).re = hardyRealZero i ^ 2 := by
      rw [xiHeatFrequency_hardyCopy, ofReal_re]
    rw [hre, hΛ]
    have h0 := (hardyRealZero_pos i).le
    have h1 := strictMono_hardyRealZero.monotone (Nat.lt_succ_iff.1 i.2)
    have h2 : hardyRealZero i ^ 2 ≤ hardyRealZero d ^ 2 := by nlinarith
    nlinarith
  set σ : ℝ := ∑ i : Fin (d + 1), ‖P.eval (xiHeatFrequency (hardyCopy i))‖ ^ 2 with hσ
  have hnodes : Real.exp (-(a * Λ)) * σ ≤ ∑' q, T q + M * ∑' q, O.indicator f q := by
    rw [hσ, Finset.mul_sum]
    exact (Finset.sum_le_sum fun i _ => hnode i).trans hlow
  -- the off-line mass is below `ε`
  have hBF : ∑' q, O.indicator f q ≤ ∑' q, ((↑F : Set XiZeroCopy)ᶜ.indicator f q) := by
    refine hBs.tsum_le_tsum (fun q => ?_) (hfs.indicator _)
    by_cases hq : q ∈ O
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show q ∈ (↑F : Set XiZeroCopy)ᶜ from
        hoffF q hq)]
    · rw [Set.indicator_of_notMem hq]
      exact Set.indicator_nonneg (fun q _ => hf0 q) q
  -- the nodes control the coefficient mass
  have hmass : coeffMass P ^ 2 ≤ K * σ := by
    have h1 := hC P hPd
    have h2 : (∑ i : Fin (d + 1), ‖P.eval (xiHeatFrequency (hardyCopy i))‖) ^ 2 ≤
        (d + 1) * σ := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (d + 1))))
        (f := fun i => ‖P.eval (xiHeatFrequency (hardyCopy i))‖)
      simpa [Finset.card_univ, Fintype.card_fin] using this
    have hc := coeffMass_nonneg P
    have hs0 : 0 ≤ ∑ i : Fin (d + 1), ‖P.eval (xiHeatFrequency (hardyCopy i))‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    calc coeffMass P ^ 2 ≤ (C * ∑ i : Fin (d + 1), ‖P.eval (xiHeatFrequency (hardyCopy i))‖) ^ 2 :=
          pow_le_pow_left₀ hc h1 2
      _ = C ^ 2 * (∑ i : Fin (d + 1), ‖P.eval (xiHeatFrequency (hardyCopy i))‖) ^ 2 := by ring
      _ ≤ C ^ 2 * ((d + 1) * σ) := mul_le_mul_of_nonneg_left h2 (sq_nonneg C)
      _ = K * σ := by rw [hK]; ring
  have hcpos := coeffMass_pos hP
  have hσpos : 0 < σ := by
    by_contra hσ0
    have : K * σ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK0 (not_lt.1 hσ0)
    nlinarith [sq_pos_of_pos hcpos]
  -- assemble
  have hexpΛ := Real.exp_pos (-(a * Λ))
  have hexpa₀ := Real.exp_pos (a₀ * Λ)
  have hMε : M * ∑' q, O.indicator f q ≤ Real.exp (-(a * Λ)) * (K * σ) / (2 * (K + 1)) := by
    have hB0 : 0 ≤ ∑' q, O.indicator f q :=
      tsum_nonneg fun q => Set.indicator_nonneg (fun q _ => hf0 q) q
    have h1 : M * ∑' q, O.indicator f q ≤ M * ε :=
      mul_le_mul_of_nonneg_left (hBF.trans hF.le) hM0
    have h2 : M * ε = coeffMass P ^ 2 * Real.exp (-(a * Λ)) / (2 * (K + 1)) := by
      rw [hM, hε]
      field_simp
    rw [h2] at h1
    refine h1.trans ?_
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  have hfinal : Real.exp (-(a * Λ)) * (K * σ) / (2 * (K + 1)) < Real.exp (-(a * Λ)) * σ := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hexpΛ hσpos]
  have hHre : (heatHankel a P P).re = ∑' q, T q := by
    rw [heatHankel, Complex.re_tsum (summable_heatHankelTermAt ha P P)]
  rw [hHre]
  linarith

/-! ## The determinant ladder -/

/-- **Height horizon of the rank-`N` determinant.**  For every rank `N` there is a height `H` such
that `Δ_N(a) > 0` for every `a > 0` whenever every off-line zero has height `> H`. -/
theorem exists_height_heatMomentDet_pos (N : ℕ) :
    ∃ H : ℝ, (∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → H < |(xiSpectralPoint q).re|) →
      ∀ a : ℝ, 0 < a → 0 < (leadingMatrix (heatMomentArray a) N).det := by
  rcases N with _ | d
  · refine ⟨0, fun _ a ha => heatMomentDet_pos_of_mul_le ha ?_⟩
    simpa using routeUCompletedPrimeGammaAperture_pos.le
  · obtain ⟨H, hH⟩ := exists_height_heatHankel_re_pos d
    exact ⟨H, fun hhigh a ha => heatMomentDet_pos_of_forall ha fun P hP hdeg =>
      hH hhigh a ha P hP (Nat.lt_succ_iff.1 hdeg)⟩

/-- **One height for the whole ladder up to rank `N`.**  Off-line zeros above `H` are invisible to
`Δ_1, …, Δ_N` at every heat time. -/
theorem exists_height_forall_le_heatMomentDet_pos (N : ℕ) :
    ∃ H : ℝ, (∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → H < |(xiSpectralPoint q).re|) →
      ∀ M ≤ N, ∀ a : ℝ, 0 < a → 0 < (leadingMatrix (heatMomentArray a) M).det := by
  choose H hH using exists_height_heatMomentDet_pos
  refine ⟨∑ M ∈ Finset.range (N + 1), |H M|, fun hhigh M hM a ha => hH M (fun q hq => ?_) a ha⟩
  have h1 : |H M| ≤ ∑ M ∈ Finset.range (N + 1), |H M| :=
    Finset.single_le_sum (fun M _ => abs_nonneg (H M)) (Finset.mem_range.2 (Nat.lt_succ_of_le hM))
  linarith [le_abs_self (H M), hhigh q hq]

/-- **Location of a nonpositive determinant.**  For every rank `N` there is a height `H` such that
`Δ_N(a) ≤ 0` at some `a > 0` forces an off-line zero of height `≤ H`. -/
theorem exists_offLine_height_le_of_heatMomentDet_nonpos (N : ℕ) :
    ∃ H : ℝ, ∀ a : ℝ, 0 < a → (leadingMatrix (heatMomentArray a) N).det ≤ 0 →
      ∃ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 ∧ |(xiSpectralPoint q).re| ≤ H := by
  obtain ⟨H, hH⟩ := exists_height_heatMomentDet_pos N
  refine ⟨H, fun a ha hdet => ?_⟩
  by_contra hno
  push Not at hno
  exact hdet.not_gt (hH hno a ha)

end

end RHTower
