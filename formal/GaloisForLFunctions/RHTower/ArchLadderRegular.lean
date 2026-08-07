import GaloisForLFunctions.RHTower.XiParityMassDichotomy

/-!
# The even ladder off the right half-plane

The closed form of the archimedean logarithmic derivative needs only that `s` avoids the poles of
`Γ(s/2)`; the right half-plane is not required.  Along the even ladder `s, s+2, s+4, …` the shift-two
identity additionally needs the archimedean factor to be nonzero, which excludes the odd integers,
where the polynomial factor `s(s-1)/2` vanishes after an even translation.

`ArchLadderRegular s` packages exactly those two conditions.  It is stable under even translation, so
the explicit rational form of the even-shift archimedean correction holds on the whole ladder — in
particular at reflected points, which lie in the left half-plane and were previously out of reach.
-/

namespace RHTower

open Complex

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- `s` avoids the poles of `Γ(s/2)` and the odd integers. -/
def ArchLadderRegular (s : ℂ) : Prop :=
  (∀ m : ℕ, s / 2 ≠ -(m : ℂ)) ∧ ∀ k : ℤ, s ≠ ((2 * k + 1 : ℤ) : ℂ)

theorem ArchLadderRegular.ne_zero {s : ℂ} (h : ArchLadderRegular s) : s ≠ 0 := by
  intro hc
  exact h.1 0 (by rw [hc]; simp)

theorem ArchLadderRegular.ne_one {s : ℂ} (h : ArchLadderRegular s) : s ≠ 1 := by
  intro hc
  exact h.2 0 (by rw [hc]; norm_num)

theorem ArchLadderRegular.ne_neg_one {s : ℂ} (h : ArchLadderRegular s) : s ≠ -1 := by
  intro hc
  exact h.2 (-1) (by rw [hc]; norm_num)

theorem ArchLadderRegular.of_re_pos {s : ℂ} (hs : 0 < s.re) (hodd : ∀ k : ℤ, s ≠ ((2 * k + 1 : ℤ) : ℂ)) :
    ArchLadderRegular s :=
  ⟨div_two_ne_neg_nat_of_re_pos hs, hodd⟩

/-- **Sharp nonvanishing of the archimedean factor.** No positivity hypothesis and no strip
hypothesis: the completed archimedean factor vanishes exactly at `1` and at the poles of `Γ(s/2)`.
The corpus's strip form is the special case where the strip supplies both clauses. -/
theorem archFactor_ne_zero_iff {s : ℂ} :
    archFactor s ≠ 0 ↔ s ≠ 1 ∧ ∀ n : ℕ, s ≠ -(2 * (n : ℂ)) := by
  constructor
  · intro h
    refine ⟨fun hc => h ?_, fun n hc => h ?_⟩
    · simp [archFactor, hc]
    · have hG : Complex.Gammaℝ s = 0 := Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, hc⟩
      simp [archFactor, hG]
  · rintro ⟨h1, hn⟩
    have hs0 : s ≠ 0 := fun hc => hn 0 (by rw [hc]; ring)
    have hG : Complex.Gammaℝ s ≠ 0 := by
      intro hc
      obtain ⟨n, hn'⟩ := Complex.Gammaℝ_eq_zero_iff.mp hc
      exact hn n hn'
    exact archFactor_ne_zero hs0 h1 hG

/-- **Strip upper bound discharged.** Positivity of the real part together with `s ≠ 1` already gives
archimedean nonvanishing; the corpus's `archFactor_ne_zero_strip` additionally assumed `Re s < 1`. -/
theorem archFactor_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    archFactor s ≠ 0 := by
  refine archFactor_ne_zero_iff.mpr ⟨h1, fun n hc => ?_⟩
  have hre : s.re = -(2 * (n : ℝ)) := by
    rw [hc]
    simp
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [hre] at hs
  linarith

/-- **The pole-free set is open.** The poles `-2n` of `Γ(z/2)` march off to infinity, so only
finitely many lie near any point; the minimum of those finitely many distances, capped at one, is a
radius that avoids all of them. -/
theorem isOpen_setOf_offPoles :
    IsOpen {z : ℂ | ∀ m : ℕ, z / 2 ≠ -(m : ℂ)} := by
  rw [Metric.isOpen_iff]
  intro z hz
  classical
  set N : ℕ := ⌈‖z‖⌉₊ + 1 with hN
  have hNne : (Finset.range N).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  set r : ℝ := min 1 ((Finset.range N).inf' hNne (fun m => ‖z + 2 * (m : ℂ)‖)) with hr
  have hpos : ∀ m : ℕ, 0 < ‖z + 2 * (m : ℂ)‖ := by
    intro m
    rw [norm_pos_iff]
    intro hc
    exact hz m (by rw [show z = -(2 * (m : ℂ)) by linear_combination hc]; ring)
  have hrpos : 0 < r := by
    refine lt_min zero_lt_one ?_
    rw [Finset.lt_inf'_iff]
    exact fun m _ => hpos m
  refine ⟨r, hrpos, fun w hw m hc => ?_⟩
  have hwz : w = -(2 * (m : ℂ)) := by linear_combination 2 * hc
  have hdist : ‖z + 2 * (m : ℂ)‖ < r := by
    have := Metric.mem_ball.mp hw
    rw [Complex.dist_eq, hwz] at this
    calc ‖z + 2 * (m : ℂ)‖ = ‖-(2 * (m : ℂ)) - z‖ := by
          rw [← norm_neg]
          congr 1
          ring
      _ < r := this
  rcases lt_or_ge m N with hmN | hmN
  · have hge : ((Finset.range N).inf' hNne (fun m => ‖z + 2 * (m : ℂ)‖))
        ≤ ‖z + 2 * (m : ℂ)‖ :=
      Finset.inf'_le _ (Finset.mem_range.mpr hmN)
    have : r ≤ ‖z + 2 * (m : ℂ)‖ := le_trans (min_le_right _ _) hge
    linarith
  · have hnorm : ‖(2 * (m : ℂ))‖ = 2 * (m : ℝ) := by
      rw [norm_mul, Complex.norm_natCast]
      norm_num
    have hkey : ‖(2 * (m : ℂ))‖ ≤ ‖z + 2 * (m : ℂ)‖ + ‖z‖ := by
      calc ‖(2 * (m : ℂ))‖ = ‖(z + 2 * (m : ℂ)) - z‖ := by congr 1; ring
        _ ≤ ‖z + 2 * (m : ℂ)‖ + ‖z‖ := norm_sub_le _ _
    have hceil : ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
    have hmge : ((⌈‖z‖⌉₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
      have : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmN
      rwa [hN, Nat.cast_add, Nat.cast_one] at this
    have hr1 : r ≤ 1 := min_le_left _ _
    rw [hnorm] at hkey
    linarith

/-- **`Γ_ℝ` is analytic off its poles.** -/
theorem analyticAt_Gammaℝ_off_poles {s : ℂ} (hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    AnalyticAt ℂ Complex.Gammaℝ s :=
  (DifferentiableOn.analyticOnNhd
    (fun _ hz => (hasDerivAt_Gammaℝ_off_poles hz).differentiableAt.differentiableWithinAt)
    isOpen_setOf_offPoles) s hpole

/-- **`archFactor` is analytic off the poles of `Γ(s/2)`.** The corpus records analyticity only on
the right half-plane (`archFactor_analyticOnNhd_re_pos`); the completed archimedean factor is in fact
analytic everywhere except at `-2, -4, …`. -/
theorem analyticAt_archFactor_off_poles {s : ℂ} (hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    AnalyticAt ℂ archFactor s :=
  (DifferentiableOn.analyticOnNhd
    (fun _ hz => (hasDerivAt_archFactor_off_poles hz).differentiableAt.differentiableWithinAt)
    isOpen_setOf_offPoles) s hpole

/-- `Γ_ℝ` is nonvanishing off the poles of `Γ(w/2)`; no positivity needed. -/
theorem Gammaℝ_ne_zero_off_poles {w : ℂ} (hpole : ∀ m : ℕ, w / 2 ≠ -(m : ℂ)) :
    Complex.Gammaℝ w ≠ 0 := by
  intro hzero
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hzero
  exact hpole n (by rw [hn]; ring)

/-- **Logarithmic derivative of `Γ_ℝ` off the poles.** The corpus's `logDeriv_Gammaℝ_of_re_pos`
assumes `0 < Re w`; only avoidance of the poles of `Γ(w/2)` is used. -/
theorem logDeriv_Gammaℝ_off_poles {w : ℂ} (hpole : ∀ m : ℕ, w / 2 ≠ -(m : ℂ)) :
    logDeriv Complex.Gammaℝ w =
      Complex.digamma (w / 2) / 2 - (Real.log Real.pi : ℂ) / 2 := by
  have hne : Complex.Gammaℝ w ≠ 0 := Gammaℝ_ne_zero_off_poles hpole
  rw [logDeriv_apply, (hasDerivAt_Gammaℝ_off_poles hpole).deriv]
  field_simp

/-- **The archimedean reflection cocycle in closed form.** The corpus derives this only locally, as
an `EventuallyEq` near `3/4` inside the curvature computation, and only where both `s` and `1 - s`
have positive real part.  It is a pointwise identity wherever both `Γ` factors are off their poles —
in particular throughout `Re s > 1` and `Re s < 0`. -/
theorem logDeriv_Gammaℝ_reflect_off_poles {s : ℂ}
    (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) (h1s : ∀ m : ℕ, (1 - s) / 2 ≠ -(m : ℂ)) :
    logDeriv (fun z : ℂ => Complex.Gammaℝ z / Complex.Gammaℝ (1 - z)) s
      = Complex.digamma (s / 2) / 2 + Complex.digamma ((1 - s) / 2) / 2
        - (Real.log Real.pi : ℂ) := by
  have hfs : Complex.Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_off_poles hs
  have hgs : Complex.Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_off_poles h1s
  have hdf : DifferentiableAt ℂ Complex.Gammaℝ s :=
    (hasDerivAt_Gammaℝ_off_poles hs).differentiableAt
  have hinner : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := (hasDerivAt_id s).const_sub 1
  have hdg : DifferentiableAt ℂ (fun z => Complex.Gammaℝ (1 - z)) s :=
    ((hasDerivAt_Gammaℝ_off_poles h1s).comp s hinner).differentiableAt
  have hLDrefl : logDeriv (fun z => Complex.Gammaℝ (1 - z)) s
      = - logDeriv Complex.Gammaℝ (1 - s) := by
    have hd : HasDerivAt (fun z : ℂ => Complex.Gammaℝ (1 - z))
        (Complex.Gammaℝ (1 - s)
          * (Complex.digamma ((1 - s) / 2) / 2 - (Real.log Real.pi : ℂ) / 2) * (-1)) s :=
      (hasDerivAt_Gammaℝ_off_poles h1s).comp s hinner
    rw [logDeriv_apply, hd.deriv, logDeriv_apply, (hasDerivAt_Gammaℝ_off_poles h1s).deriv]
    ring
  rw [logDeriv_div (f := Complex.Gammaℝ) (g := fun z => Complex.Gammaℝ (1 - z)) s hfs hgs hdf hdg,
    hLDrefl, logDeriv_Gammaℝ_off_poles hs, logDeriv_Gammaℝ_off_poles h1s]
  ring

/-- **Logarithmic derivative of a translated `Γ_ℝ` factor.** This is the digamma mode carried by the
factor `Γ_ℝ(s + κ)` of a completed L-function. -/
theorem logDeriv_Gammaℝ_translate_off_poles {κ s : ℂ}
    (hpole : ∀ m : ℕ, (s + κ) / 2 ≠ -(m : ℂ)) :
    logDeriv (fun z => Complex.Gammaℝ (z + κ)) s =
      Complex.digamma ((s + κ) / 2) / 2 - (Real.log Real.pi : ℂ) / 2 := by
  rw [logDeriv_apply, deriv_comp_add_const, ← logDeriv_apply,
    logDeriv_Gammaℝ_off_poles hpole]

/-- **The polynomial factor contributes nothing to the archimedean reflection.** Summing the
completed archimedean logarithmic derivative with its reflection cancels the rational part
`1/s + 1/(s-1)` exactly, leaving the pure `Γ_ℝ` weld `logDeriv (z ↦ Γ_ℝ z / Γ_ℝ(1-z))`.  So the
reflection defect of `archFactor` is carried entirely by the Gamma factor. -/
theorem logDeriv_archFactor_add_reflect {s : ℂ}
    (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) (h1s : ∀ m : ℕ, (1 - s) / 2 ≠ -(m : ℂ))
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    logDeriv archFactor s + logDeriv archFactor (1 - s)
      = logDeriv (fun z : ℂ => Complex.Gammaℝ z / Complex.Gammaℝ (1 - z)) s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h1s0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1s1 : (1 : ℂ) - s ≠ 1 := fun hc => h0 (by linear_combination -hc)
  rw [logDeriv_archFactor_closed_off_poles hs h0 h1,
    logDeriv_archFactor_closed_off_poles h1s h1s0 h1s1,
    logDeriv_Gammaℝ_reflect_off_poles hs h1s,
    gammaRealLogConnection, gammaRealLogConnection,
    show (1 : ℂ) - s - 1 = -s by ring]
  field_simp
  ring

/-- **Independence of the logarithmic derivatives of the Gamma factors of a completed L-function.**
No `ℂ`-combination of `logDeriv (z ↦ Γ_ℝ(z + κⱼ))` is a rational function unless it is trivial, as
soon as no two exponents differ by an even integer.  The constant `-log π/2` carried by every factor
is absorbed into the rational side, so it obstructs nothing. -/
theorem logDeriv_Gammaℝ_translates_independent {d : ℕ} {κ E : Fin d → ℂ}
    (hsep : ∀ i j : Fin d, i ≠ j → ∀ m : ℤ, κ i - κ j ≠ ((2 * m : ℤ) : ℂ))
    {P Q : Polynomial ℂ} (hQ : Q ≠ 0) (hco : IsCoprime P Q) {T : Set ℂ} (hT : T.Finite)
    (h : ∀ s : ℂ, (∀ i, 0 < (s + κ i).re) → s ∉ T → Q.eval s ≠ 0 →
      ∑ i, E i * logDeriv (fun z => Complex.Gammaℝ (z + κ i)) s = P.eval s / Q.eval s) :
    ∀ i, E i = 0 := by
  classical
  set c : ℂ := ((Real.log Real.pi : ℝ) : ℂ) / 2 * (∑ i, E i) with hc_def
  have hkey := GaloisForLFunctions.HTGeometry.digamma_halfArgument_modes_independent
    (κ := κ) (E := fun i => E i / 2) hsep (P := P + Q * Polynomial.C c) hQ
    (hco.add_mul_left_left (Polynomial.C c)) hT ?_
  · intro i
    have hi := hkey i
    linear_combination 2 * hi
  · intro s hs hsT hQs
    have hmode : ∀ i, logDeriv (fun z => Complex.Gammaℝ (z + κ i)) s
        = Complex.digamma ((s + κ i) / 2) / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2 := fun i =>
      logDeriv_Gammaℝ_translate_off_poles (div_two_ne_neg_nat_of_re_pos (hs i))
    have hval := h s hs hsT hQs
    rw [Finset.sum_congr rfl fun i _ => by rw [hmode i]] at hval
    have hsplit : ∑ i, E i *
          (Complex.digamma ((s + κ i) / 2) / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2)
        = (∑ i, E i / 2 * Complex.digamma ((s + κ i) / 2)) -
          ((Real.log Real.pi : ℝ) : ℂ) / 2 * (∑ i, E i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, eq_div_iff hQs] at hval
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hc_def, eq_div_iff hQs]
    linear_combination hval

/-- **Ladder regularity is automatic off the integer real parts.** Both conditions force the real
part to be an integer, so a non-integral real part discharges them together — with no positivity
requirement. -/
theorem archLadderRegular_of_re_not_int {s : ℂ} (hint : ∀ k : ℤ, s.re ≠ (k : ℝ)) :
    ArchLadderRegular s := by
  refine ⟨fun m hc => hint (-(2 * m : ℤ)) ?_, fun k hc => hint (2 * k + 1) ?_⟩
  · have hs : s = -(2 * (m : ℂ)) := by linear_combination 2 * hc
    rw [hs]
    push_cast
    simp
  · rw [hc]
    push_cast
    simp

/-- A real part strictly between consecutive integers discharges ladder regularity. -/
theorem archLadderRegular_of_re_mem_Ioo {s : ℂ} {n : ℤ}
    (h0 : (n : ℝ) < s.re) (h1 : s.re < (n : ℝ) + 1) : ArchLadderRegular s := by
  refine archLadderRegular_of_re_not_int fun k hk => ?_
  rw [hk] at h0 h1
  have hk0 : n < k := by exact_mod_cast h0
  have hk1 : k < n + 1 := by exact_mod_cast h1
  omega

/-- **Strip translates are ladder regular.** Every natural translate of a point of the open critical
strip discharges the hypothesis. -/
theorem archLadderRegular_strip_add_nat {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (b : ℕ) :
    ArchLadderRegular (ρ + (b : ℂ)) := by
  refine archLadderRegular_of_re_mem_Ioo (n := (b : ℤ)) ?_ ?_ <;>
    rw [Complex.add_re, Complex.natCast_re] <;> push_cast <;> linarith

/-- **Reflected strip points are ladder regular.** -/
theorem archLadderRegular_strip_reflect {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (a : ℕ) :
    ArchLadderRegular (1 - (a : ℂ) - ρ) := by
  refine archLadderRegular_of_re_mem_Ioo (n := -(a : ℤ)) ?_ ?_ <;>
    rw [Complex.sub_re, Complex.sub_re, Complex.one_re, Complex.natCast_re] <;>
    push_cast <;> linarith

/-- **Archimedean nonvanishing on the ladder, discharged.** Ladder regularity already implies the
archimedean factor is nonzero, so no separate nonvanishing side condition is needed anywhere on the
even ladder — including at reflected points in the left half-plane. -/
theorem archFactor_ne_zero_of_ladderRegular {s : ℂ} (h : ArchLadderRegular s) :
    archFactor s ≠ 0 :=
  archFactor_ne_zero_iff.mpr ⟨h.ne_one, fun n hc => h.1 n (by rw [hc]; ring)⟩

/-- Even translation preserves ladder regularity. -/
theorem ArchLadderRegular.shift {s : ℂ} (h : ArchLadderRegular s) (j : ℕ) :
    ArchLadderRegular (s + ((2 * j : ℕ) : ℂ)) := by
  refine ⟨fun m hc => h.1 (m + j) ?_, fun k hc => h.2 (k - j) ?_⟩
  · push_cast at hc ⊢
    linear_combination hc
  · push_cast at hc ⊢
    linear_combination hc

/-- **Shift-two archimedean correction off the poles.** -/
theorem logDeriv_archFactor_shift_two_of_ladderRegular {s : ℂ} (h : ArchLadderRegular s) :
    logDeriv archFactor (s + 2) - logDeriv archFactor s =
      1 / (s + 2) + 1 / (s + 1) - 1 / (s - 1) := by
  have hs0 : s ≠ 0 := h.ne_zero
  have hs1 : s ≠ 1 := h.ne_one
  have hsm1 : s ≠ -1 := h.ne_neg_one
  have hs2 : s + 2 ≠ 0 := by
    intro hc
    refine h.1 1 ?_
    push_cast
    linear_combination hc / 2
  have hs3 : s + 2 ≠ 1 := by
    intro hc
    exact hsm1 (by linear_combination hc)
  have hpole2 : ∀ m : ℕ, (s + 2) / 2 ≠ -(m : ℂ) := by
    intro m hc
    refine h.1 (m + 1) ?_
    push_cast
    linear_combination hc
  rw [logDeriv_archFactor_closed_off_poles hpole2 hs2 hs3,
    logDeriv_archFactor_closed_off_poles h.1 hs0 hs1,
    show (s + 2) - 1 = s + 1 by ring]
  unfold gammaRealLogConnection
  rw [show (s + 2) / 2 = s / 2 + 1 by ring,
    GaloisForLFunctions.digamma_half_add_one h.1]
  field_simp [hs0, hs1, hs2, sub_ne_zero.mpr hs1]
  ring

/-- **Even-shift archimedean correction off the poles.** The rational telescope is valid on the whole
even ladder, not merely on the right half-plane. -/
theorem xiTransverseShiftArchimedeanCorrection_even_of_ladderRegular {s : ℂ}
    (h : ArchLadderRegular s) (m : ℕ) :
    xiTransverseShiftArchimedeanCorrection (2 * m) s = xiEvenShiftPrimeCorrection m s := by
  induction m with
  | zero => simp [xiTransverseShiftArchimedeanCorrection, xiEvenShiftPrimeCorrection]
  | succ m ih =>
      have hstep := logDeriv_archFactor_shift_two_of_ladderRegular (h.shift m)
      have hcast : ((2 * (m + 1) : ℕ) : ℂ) = ((2 * m : ℕ) : ℂ) + 2 := by push_cast; ring
      have hcorr : xiEvenShiftPrimeCorrection (m + 1) s =
          xiEvenShiftPrimeCorrection m s +
            (1 / (s + ((2 * m : ℕ) : ℂ) + 2) + 1 / (s + ((2 * m : ℕ) : ℂ) + 1) -
              1 / (s + ((2 * m : ℕ) : ℂ) - 1)) := by
        rw [xiEvenShiftPrimeCorrection, xiEvenShiftPrimeCorrection, Finset.sum_range_succ]
      rw [xiTransverseShiftArchimedeanCorrection] at ih ⊢
      rw [hcast, hcorr, show s + (((2 * m : ℕ) : ℂ) + 2) = s + ((2 * m : ℕ) : ℂ) + 2 by ring]
      linear_combination hstep + ih

/-- **Same-parity pairwise archimedean correction off the poles.** -/
theorem xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_of_ladderRegular
    {a b : ℕ} (hba : b ≤ a) (hpar : a % 2 = b % 2) {s : ℂ}
    (h : ArchLadderRegular (s + (b : ℂ))) :
    xiPairwiseShiftArchimedeanCorrectionDifference a b s =
      xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) := by
  obtain ⟨m, hm⟩ : ∃ m, a - b = 2 * m := ⟨(a - b) / 2, by omega⟩
  rw [xiPairwiseShiftArchimedeanCorrectionDifference_eq_relativeShift_of_le a b s hba, hm,
    xiTransverseShiftArchimedeanCorrection_even_of_ladderRegular h m]
  congr 1
  omega

@[simp]
theorem xiEvenShiftPrimeCorrection_zero (t : ℂ) : xiEvenShiftPrimeCorrection 0 t = 0 := by
  simp [xiEvenShiftPrimeCorrection]

/-- **Endpoint order discharged.** Truncated subtraction makes the same-parity pairwise archimedean
correction order-free: exactly one of the two telescopes is nonempty, and the empty one contributes
nothing. -/
theorem xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_symm
    {a b : ℕ} (hpar : a % 2 = b % 2) {s : ℂ}
    (h : ArchLadderRegular (s + ((min a b : ℕ) : ℂ))) :
    xiPairwiseShiftArchimedeanCorrectionDifference a b s =
      xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) -
        xiEvenShiftPrimeCorrection ((b - a) / 2) (s + (a : ℂ)) := by
  rcases le_total b a with hba | hab
  · rw [show (min a b : ℕ) = b by omega] at h
    rw [show (b - a) / 2 = 0 by omega, xiEvenShiftPrimeCorrection_zero, sub_zero,
      xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_of_ladderRegular hba hpar h]
  · rw [show (min a b : ℕ) = a by omega] at h
    rw [show (a - b) / 2 = 0 by omega, xiEvenShiftPrimeCorrection_zero, zero_sub,
      xiPairwiseShiftArchimedeanCorrectionDifference_swap b a,
      xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_of_ladderRegular hab hpar.symm h]

/-- **Endpoint order discharged for the corrected pairwise value.** -/
theorem xiPairwiseShiftPrimeDifference_eq_explicit_symm
    {a b : ℕ} (hpar : a % 2 = b % 2) {s : ℂ}
    (h : ArchLadderRegular (s + ((min a b : ℕ) : ℂ))) :
    xiPairwiseShiftPrimeDifference a b s =
      (logDeriv xi (s + (a : ℂ)) - logDeriv xi (s + (b : ℂ))) -
        (xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) -
          xiEvenShiftPrimeCorrection ((b - a) / 2) (s + (a : ℂ))) := by
  rw [xiPairwiseShiftPrimeDifference_eq_raw_sub_correction,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_symm hpar h,
    xiPairwiseShiftRawLogDerivDifference]

/-- **Explicit rational reflection cocycle for a same-parity pair.** Both the base point and its
reflection are handled: the reflected point lies in the left half-plane, which the ladder-regular
form reaches. -/
theorem xiPairwiseShiftReflectionCocycle_eq_explicit
    {a b : ℕ} (hba : b ≤ a) (hpar : a % 2 = b % 2) {s : ℂ}
    (hbase : ArchLadderRegular (s + (b : ℂ)))
    (hrefl : ArchLadderRegular (1 - (a : ℂ) - s)) :
    xiPairwiseShiftReflectionCocycle a b s =
      xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) -
        xiEvenShiftPrimeCorrection ((a - b) / 2) (1 - (a : ℂ) - s) := by
  have hrefl' : ArchLadderRegular (xiPairwiseShiftReflection (a : ℂ) (b : ℂ) s + (b : ℂ)) := by
    rw [xiPairwiseShiftReflection, show (1 : ℂ) - a - b - s + b = 1 - (a : ℂ) - s by ring]
    exact hrefl
  rw [xiPairwiseShiftReflectionCocycle,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_of_ladderRegular hba hpar hbase,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_of_ladderRegular hba hpar hrefl',
    xiPairwiseShiftReflection, show (1 : ℂ) - a - b - s + b = 1 - (a : ℂ) - s by ring]

/-- **Same-parity corrected pairwise value off the poles.** -/
theorem xiPairwiseShiftPrimeDifference_eq_explicit_of_ladderRegular
    {a b : ℕ} (hba : b ≤ a) (hpar : a % 2 = b % 2) {s : ℂ}
    (h : ArchLadderRegular (s + (b : ℂ))) :
    xiPairwiseShiftPrimeDifference a b s =
      (logDeriv xi (s + (a : ℂ)) - logDeriv xi (s + (b : ℂ))) -
        xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) := by
  rw [xiPairwiseShiftPrimeDifference_eq_raw_sub_correction,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_of_ladderRegular hba hpar h,
    xiPairwiseShiftRawLogDerivDifference]

/-- **Explicit centered value for a same-parity pair.** Half-cocycle centering subtracts the average
of the rational telescope at the point and at its reflection.  The correction is manifestly rational
and manifestly symmetric about `(1-a-b)/2`; the completed-Xi content is the raw logarithmic-derivative
difference alone.

The corpus shift-two theory is the pair `(2,0)`: there the average of the telescope at `s` and at
`-1-s` is `1/(s+2) + 1/(s+1) - 1/(s-1) - (1/2)(1/s + 1/(s+1))`. -/
theorem xiPairwiseCenteredShiftPrimeDifference_eq_explicit
    {a b : ℕ} (hba : b ≤ a) (hpar : a % 2 = b % 2) {s : ℂ}
    (hbase : ArchLadderRegular (s + (b : ℂ)))
    (hrefl : ArchLadderRegular (1 - (a : ℂ) - s)) :
    xiPairwiseCenteredShiftPrimeDifference a b s =
      (logDeriv xi (s + (a : ℂ)) - logDeriv xi (s + (b : ℂ))) -
        (1 / 2 : ℂ) * (xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) +
          xiEvenShiftPrimeCorrection ((a - b) / 2) (1 - (a : ℂ) - s)) := by
  rw [xiPairwiseCenteredShiftPrimeDifference,
    xiPairwiseShiftPrimeDifference_eq_explicit_of_ladderRegular hba hpar hbase,
    xiPairwiseShiftReflectionCocycle_eq_explicit hba hpar hbase hrefl]
  ring

/-- The reflected even-shift telescope is half-plane rational. -/
theorem isHalfPlaneRational_xiEvenShiftPrimeCorrection_reflected (m : ℕ) (γ : ℂ) :
    IsHalfPlaneRational (fun s : ℂ => xiEvenShiftPrimeCorrection m (γ - s)) := by
  have hterm : ∀ j : ℕ, IsHalfPlaneRational
      (fun s : ℂ => -(1 / (s + -(γ + ((2 * j : ℕ) : ℂ) + 2))) +
        -(1 / (s + -(γ + ((2 * j : ℕ) : ℂ) + 1))) -
        -(1 / (s + -(γ + ((2 * j : ℕ) : ℂ) - 1)))) := fun j =>
    ((isHalfPlaneRational_simple _).neg.add (isHalfPlaneRational_simple _).neg).sub
      (isHalfPlaneRational_simple _).neg
  have hsum := isHalfPlaneRational_finsetSum (Finset.range m) _ (fun j _ => hterm j)
  refine IsHalfPlaneRational.congr Set.finite_empty (fun z _ _ => ?_) hsum
  rw [xiEvenShiftPrimeCorrection]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show γ - z + ((2 * j : ℕ) : ℂ) + 2 = -(z + -(γ + ((2 * j : ℕ) : ℂ) + 2)) by ring,
    show γ - z + ((2 * j : ℕ) : ℂ) + 1 = -(z + -(γ + ((2 * j : ℕ) : ℂ) + 1)) by ring,
    show γ - z + ((2 * j : ℕ) : ℂ) - 1 = -(z + -(γ + ((2 * j : ℕ) : ℂ) - 1)) by ring,
    div_neg, div_neg, div_neg]

/-- **Pointwise even-shift defect identification off the poles.** The corpus records this only as an
upper-end germ; on the whole even ladder it is a pointwise identity. -/
theorem xiEvenShiftPrimeDefect_eq_xiTransverseShiftPrimeDefect_of_ladderRegular
    {s : ℂ} (h : ArchLadderRegular s) (m : ℕ) :
    xiEvenShiftPrimeDefect m s = xiTransverseShiftPrimeDefect (2 * m) s := by
  rw [xiEvenShiftPrimeDefect, xiTransverseShiftPrimeDefect,
    xiTransverseShiftRawLogDerivDefect,
    xiTransverseShiftArchimedeanCorrection_even_of_ladderRegular h m]

/-! ## Side conditions discharged on the critical strip -/

/-- Points of the open critical strip are ladder regular. -/
theorem archLadderRegular_of_strip {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ArchLadderRegular ρ := by
  simpa using archLadderRegular_strip_add_nat h0 h1 0

/-- **Pointwise even-shift defect identification at a strip point, side conditions discharged.** -/
theorem xiEvenShiftPrimeDefect_eq_xiTransverseShiftPrimeDefect_of_strip
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (m : ℕ) :
    xiEvenShiftPrimeDefect m ρ = xiTransverseShiftPrimeDefect (2 * m) ρ :=
  xiEvenShiftPrimeDefect_eq_xiTransverseShiftPrimeDefect_of_ladderRegular
    (archLadderRegular_of_strip h0 h1) m


/-- **Explicit reflection cocycle at a strip point, side conditions discharged.** -/
theorem xiPairwiseShiftReflectionCocycle_eq_explicit_of_strip
    {a b : ℕ} (hba : b ≤ a) (hpar : a % 2 = b % 2) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    xiPairwiseShiftReflectionCocycle a b ρ =
      xiEvenShiftPrimeCorrection ((a - b) / 2) (ρ + (b : ℂ)) -
        xiEvenShiftPrimeCorrection ((a - b) / 2) (1 - (a : ℂ) - ρ) :=
  xiPairwiseShiftReflectionCocycle_eq_explicit hba hpar
    (archLadderRegular_strip_add_nat h0 h1 b) (archLadderRegular_strip_reflect h0 h1 a)

/-- **Explicit corrected pairwise value at a strip point, side conditions discharged.** -/
theorem xiPairwiseShiftPrimeDifference_eq_explicit_of_strip
    {a b : ℕ} (hpar : a % 2 = b % 2) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    xiPairwiseShiftPrimeDifference a b ρ =
      (logDeriv xi (ρ + (a : ℂ)) - logDeriv xi (ρ + (b : ℂ))) -
        (xiEvenShiftPrimeCorrection ((a - b) / 2) (ρ + (b : ℂ)) -
          xiEvenShiftPrimeCorrection ((b - a) / 2) (ρ + (a : ℂ))) :=
  xiPairwiseShiftPrimeDifference_eq_explicit_symm hpar
    (archLadderRegular_strip_add_nat h0 h1 (min a b))

/-- **Explicit centered pairwise value at a strip point, side conditions discharged.** The centered
value differs from the raw completed-Xi logarithmic-derivative difference by an explicit rational
function, at every point of the open critical strip. -/
theorem xiPairwiseCenteredShiftPrimeDifference_eq_explicit_of_strip
    {a b : ℕ} (hba : b ≤ a) (hpar : a % 2 = b % 2) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    xiPairwiseCenteredShiftPrimeDifference a b ρ =
      (logDeriv xi (ρ + (a : ℂ)) - logDeriv xi (ρ + (b : ℂ))) -
        (1 / 2 : ℂ) * (xiEvenShiftPrimeCorrection ((a - b) / 2) (ρ + (b : ℂ)) +
          xiEvenShiftPrimeCorrection ((a - b) / 2) (1 - (a : ℂ) - ρ)) :=
  xiPairwiseCenteredShiftPrimeDifference_eq_explicit hba hpar
    (archLadderRegular_strip_add_nat h0 h1 b) (archLadderRegular_strip_reflect h0 h1 a)

/-- **The centering correction of a same-parity pair is half-plane rational.** -/
theorem isHalfPlaneRational_pairwiseCenteringCorrection (a b : ℕ) :
    IsHalfPlaneRational (fun s : ℂ =>
      (1 / 2 : ℂ) * (xiEvenShiftPrimeCorrection ((a - b) / 2) (s + (b : ℂ)) +
        xiEvenShiftPrimeCorrection ((a - b) / 2) (1 - (a : ℂ) - s))) :=
  ((isHalfPlaneRational_xiEvenShiftPrimeCorrection ((a - b) / 2) (b : ℂ)).add
    (isHalfPlaneRational_xiEvenShiftPrimeCorrection_reflected ((a - b) / 2)
      (1 - (a : ℂ)))).const_mul _

end

end RHTower
