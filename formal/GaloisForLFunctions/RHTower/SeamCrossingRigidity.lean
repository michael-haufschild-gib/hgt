/-
Crossing rigidity of the finite carrier on the critical line.

The completed truncation `completedGN = archFactor·gN` is real on the critical line, and its
archimedean factor never vanishes there, so an on-line point where its real part vanishes is
exactly an on-line carrier zero.  The winding-phase / Borel–Carathéodory segment-length laws
cap the length of any on-line stretch that stays sign-constant (crossing-free) by
`(π + BC-budget)/windingFloor`, a bound that shrinks like `1/log T` with the height.

Read as a constraint on the seam: a critical-line segment longer than that bound cannot be
crossing-free — it is forced to carry an on-line carrier zero.  Every stretch of the segment
longer than the bound carries one, so the on-line zeros recur at the `1/log T` scale (the
oscillation scale), and a zero-free carrier disc forces the seam segment inside it to be short.
The combinatorial companion turns a uniform "no crossing-free stretch exceeds `Λ`" datum over
a segment into a lower bound on the number of strictly ordered on-line zeros it carries.
-/
import GaloisForLFunctions.RHTower.RadiusScaleForcing

open Complex Metric

namespace RHTower

/-! ### §1 Reality on the line: a real-part zero is a carrier zero -/

/-- On the critical line, a point where the real part of the completed truncation vanishes is
a zero of the finite carrier: the completed truncation is real there and its archimedean
factor never vanishes on the line. -/
private theorem gN_line_eq_zero_of_completedGN_re_eq_zero {N : ℕ} {τ : ℝ}
    (h : (completedGN N (linePt τ)).re = 0) : gN N (linePt τ) = 0 := by
  have him : (completedGN N (linePt τ)).im = 0 :=
    completedGN_im_eq_zero_on_line (linePt_re τ)
  have hz : completedGN N (linePt τ) = 0 :=
    Complex.ext (by simpa using h) (by simpa using him)
  have hz' : archFactor (linePt τ) * gN N (linePt τ) = 0 := hz
  exact (mul_eq_zero.mp hz').resolve_left (archFactor_linePt_ne_zero τ)

/-- Conversely, a carrier zero on the line is a real-part zero of the completed truncation. -/
private theorem completedGN_re_eq_zero_of_gN_line_eq_zero {N : ℕ} {τ : ℝ}
    (h : gN N (linePt τ) = 0) : (completedGN N (linePt τ)).re = 0 := by
  have hz : completedGN N (linePt τ) = 0 := by
    show archFactor (linePt τ) * gN N (linePt τ) = 0
    rw [h, mul_zero]
  rw [hz, Complex.zero_re]

/-- On the line, a real-part zero of the completed truncation is a genuine zero of it: the
completed truncation is real there. -/
private theorem completedGN_line_eq_zero_of_re_eq_zero {N : ℕ} {τ : ℝ}
    (h : (completedGN N (linePt τ)).re = 0) : completedGN N (linePt τ) = 0 :=
  Complex.ext (by simpa using h) (by simpa using completedGN_im_eq_zero_on_line (linePt_re τ))

/-! ### §2 Forced crossing on a long seam segment -/

/-- **Forced crossing (one-zero disc).**  If a critical-line segment `[a,b]` sits inside a disc
where the finite carrier factors through a single point with nowhere-zero difference quotient,
and the segment is longer than the one-zero segment-length bound `(π + BC-budget)/windingFloor`,
then the segment carries an on-line real-part zero of the completed truncation.  It is the
contrapositive of the one-zero segment-length law: a crossing-free segment would have to be
short. -/
theorem seam_edge_forced_online_zero_one_zero (N : ℕ)
    {τc a b R Md : ℝ} {ρ' : ℂ} (hR0 : 0 < R) (ha : 0 < a)
    (hflr : 0 < (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
    (hd_an : AnalyticOnNhd ℂ (dslope (gN N) ρ') (ball (linePt τc) R))
    (hd_ne : ∀ z ∈ ball (linePt τc) R, dslope (gN N) ρ' z ≠ 0)
    (hfact : ∀ z ∈ ball (linePt τc) R, gN N z = (z - ρ') * dslope (gN N) ρ' z)
    (hMd : ∀ z ∈ ball (linePt τc) R, ‖dslope (gN N) ρ' z‖ ≤ Md)
    (hltd : ‖dslope (gN N) ρ' (linePt τc)‖ < Md)
    (hab : a ≤ b)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R)
    (hlong :
      (Real.pi + (2 * |a - τc| / (R - |a - τc|) + 2 * |b - τc| / (R - |b - τc|)) *
          (Real.log Md - Real.log ‖dslope (gN N) ρ' (linePt τc)‖)) /
        ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2) < b - a) :
    ∃ τ ∈ Set.Icc a b, (completedGN N (linePt τ)).re = 0 := by
  by_contra hcon
  push Not at hcon
  have hlaw := sign_constant_segment_length_le_one_zero N hR0 ha hflr hd_an hd_ne hfact
    hMd hltd hab hseg hcon
  linarith

/-- **Forced carrier crossing (one-zero disc).**  The carrier form of the forced crossing: a
long crossing-free-impossible segment carries an actual on-line zero of the finite carrier. -/
theorem seam_edge_forced_crossing_one_zero (N : ℕ)
    {τc a b R Md : ℝ} {ρ' : ℂ} (hR0 : 0 < R) (ha : 0 < a)
    (hflr : 0 < (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
    (hd_an : AnalyticOnNhd ℂ (dslope (gN N) ρ') (ball (linePt τc) R))
    (hd_ne : ∀ z ∈ ball (linePt τc) R, dslope (gN N) ρ' z ≠ 0)
    (hfact : ∀ z ∈ ball (linePt τc) R, gN N z = (z - ρ') * dslope (gN N) ρ' z)
    (hMd : ∀ z ∈ ball (linePt τc) R, ‖dslope (gN N) ρ' z‖ ≤ Md)
    (hltd : ‖dslope (gN N) ρ' (linePt τc)‖ < Md)
    (hab : a ≤ b)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R)
    (hlong :
      (Real.pi + (2 * |a - τc| / (R - |a - τc|) + 2 * |b - τc| / (R - |b - τc|)) *
          (Real.log Md - Real.log ‖dslope (gN N) ρ' (linePt τc)‖)) /
        ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2) < b - a) :
    ∃ τ ∈ Set.Icc a b, gN N (linePt τ) = 0 := by
  obtain ⟨τ, hτ, hzero⟩ := seam_edge_forced_online_zero_one_zero N hR0 ha hflr hd_an hd_ne
    hfact hMd hltd hab hseg hlong
  exact ⟨τ, hτ, gN_line_eq_zero_of_completedGN_re_eq_zero hzero⟩

/-- **Forced completed-carrier crossing (one-zero disc).**  The ledger form of the forced
crossing: a long segment carries an on-line zero of the completed truncation itself — the
on-seam zero the seam ledger charges. -/
theorem seam_edge_forced_completedGN_zero_one_zero (N : ℕ)
    {τc a b R Md : ℝ} {ρ' : ℂ} (hR0 : 0 < R) (ha : 0 < a)
    (hflr : 0 < (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
    (hd_an : AnalyticOnNhd ℂ (dslope (gN N) ρ') (ball (linePt τc) R))
    (hd_ne : ∀ z ∈ ball (linePt τc) R, dslope (gN N) ρ' z ≠ 0)
    (hfact : ∀ z ∈ ball (linePt τc) R, gN N z = (z - ρ') * dslope (gN N) ρ' z)
    (hMd : ∀ z ∈ ball (linePt τc) R, ‖dslope (gN N) ρ' z‖ ≤ Md)
    (hltd : ‖dslope (gN N) ρ' (linePt τc)‖ < Md)
    (hab : a ≤ b)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R)
    (hlong :
      (Real.pi + (2 * |a - τc| / (R - |a - τc|) + 2 * |b - τc| / (R - |b - τc|)) *
          (Real.log Md - Real.log ‖dslope (gN N) ρ' (linePt τc)‖)) /
        ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2) < b - a) :
    ∃ τ ∈ Set.Icc a b, completedGN N (linePt τ) = 0 := by
  obtain ⟨τ, hτ, hzero⟩ := seam_edge_forced_online_zero_one_zero N hR0 ha hflr hd_an hd_ne
    hfact hMd hltd hab hseg hlong
  exact ⟨τ, hτ, completedGN_line_eq_zero_of_re_eq_zero hzero⟩

/-! ### §3 Zero-free rigidity: a zero-free disc forces the seam segment short -/

/-- Inside a zero-free carrier disc, the completed truncation has nonzero real part at every
on-line point of the disc: the carrier is nonzero, the archimedean factor is nonzero, and the
product is real on the line, so its real part cannot vanish. -/
theorem online_re_ne_zero_of_zero_free {N : ℕ} {τc R τ : ℝ}
    (hzf : ∀ z ∈ ball (linePt τc) R, gN N z ≠ 0)
    (hmem : linePt τ ∈ ball (linePt τc) R) :
    (completedGN N (linePt τ)).re ≠ 0 := fun h0 =>
  hzf (linePt τ) hmem (gN_line_eq_zero_of_completedGN_re_eq_zero h0)

/-- **Zero-free rigidity.**  A carrier disc with no zeros forces its critical-line segment to be
short: its length is at most the zero-free segment-length bound
`BC-budget/windingFloor`.  The crossing-free hypothesis of the segment-length law is automatic
here — there is nothing to cross — so the bound holds unconditionally on such a segment. -/
theorem zerofree_seam_edge_length_le (N : ℕ)
    {τc a b R M : ℝ} (hR0 : 0 < R) (ha : 0 < a)
    (hflr : 0 < (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
    (hball : ∀ z ∈ ball (linePt τc) R, z.re < 1)
    (hzf : ∀ z ∈ ball (linePt τc) R, gN N z ≠ 0)
    (hM : ∀ z ∈ ball (linePt τc) R, ‖gN N z‖ ≤ M)
    (hlt : ‖gN N (linePt τc)‖ < M)
    (hab : a ≤ b)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R) :
    b - a ≤
      (2 * |a - τc| / (R - |a - τc|) + 2 * |b - τc| / (R - |b - τc|)) *
          (Real.log M - Real.log ‖gN N (linePt τc)‖) /
        ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2) :=
  sign_constant_segment_length_le N hR0 ha hflr hball hzf hM hlt hab hseg
    (fun τ hτ => online_re_ne_zero_of_zero_free hzf (hseg τ hτ))

/-! ### §4 The oscillation scale over a whole segment -/

/-- A window distance bound at the two endpoints bounds the distance at every interior point. -/
theorem abs_sub_le_of_mem_Icc_endpoints {a b τc ρmax x : ℝ}
    (hρa : |a - τc| ≤ ρmax) (hρb : |b - τc| ≤ ρmax) (hx : x ∈ Set.Icc a b) :
    |x - τc| ≤ ρmax := by
  rw [Set.mem_Icc] at hx
  rw [abs_le] at hρa hρb ⊢
  exact ⟨by linarith [hρa.1, hx.1], by linarith [hρb.2, hx.2]⟩

/-- The Borel–Carathéodory prefactor `2|x|/(R − |x|)` is monotone in the endpoint distance. -/
theorem prefactor_mono {R ρmax x : ℝ} (hR0 : 0 < R) (hxρ : |x| ≤ ρmax) (hρR : ρmax < R) :
    2 * |x| / (R - |x|) ≤ 2 * ρmax / (R - ρmax) := by
  have hden1 : 0 < R - |x| := by linarith [le_trans hxρ hρR.le]
  have hden2 : 0 < R - ρmax := by linarith
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith [mul_le_mul_of_nonneg_right hxρ hR0.le, abs_nonneg x]

/-- **The seam oscillation scale (one-zero disc).**  For a critical-line window `[a,b]` inside a
one-zero carrier disc, no crossing-free sub-stretch is longer than the uniform bound
`Λ = (π + (4ρmax/(R − ρmax))·(log Md − log‖dslope center‖))/windingFloor(a)`: every sub-stretch
of `[a,b]` longer than `Λ` carries an on-line real-part zero of the completed truncation.
Mechanism: on each sub-stretch the one-zero segment-length bound applies; its Borel–Carathéodory
prefactor is monotone in the endpoint distance (hence `≤ 4ρmax/(R − ρmax)`) and its winding floor
is monotone in the height (hence `≥ windingFloor(a)`), so the per-sub-stretch bound is at most the
uniform `Λ`. -/
theorem seam_no_long_sign_constant_stretch_one_zero (N : ℕ)
    {τc a b R Md ρmax : ℝ} {ρ' : ℂ} (hR0 : 0 < R) (ha : 0 < a)
    (hflr : 0 < (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
    (hd_an : AnalyticOnNhd ℂ (dslope (gN N) ρ') (ball (linePt τc) R))
    (hd_ne : ∀ z ∈ ball (linePt τc) R, dslope (gN N) ρ' z ≠ 0)
    (hfact : ∀ z ∈ ball (linePt τc) R, gN N z = (z - ρ') * dslope (gN N) ρ' z)
    (hMd : ∀ z ∈ ball (linePt τc) R, ‖dslope (gN N) ρ' z‖ ≤ Md)
    (hltd : ‖dslope (gN N) ρ' (linePt τc)‖ < Md)
    (hρa : |a - τc| ≤ ρmax) (hρb : |b - τc| ≤ ρmax) (hρR : ρmax < R)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R) :
    ∀ c d, a ≤ c → c ≤ d → d ≤ b →
      (Real.pi + 4 * ρmax / (R - ρmax) *
          (Real.log Md - Real.log ‖dslope (gN N) ρ' (linePt τc)‖)) /
        ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2) < d - c →
      ∃ τ ∈ Set.Icc c d, (completedGN N (linePt τ)).re = 0 := by
  intro c d hac hcd hdb hlongcd
  set L : ℝ := Real.log Md - Real.log ‖dslope (gN N) ρ' (linePt τc)‖ with hL_def
  have hd0 : 0 < ‖dslope (gN N) ρ' (linePt τc)‖ :=
    norm_pos_iff.mpr (hd_ne _ (mem_ball_self hR0))
  have hL0 : 0 ≤ L := by rw [hL_def]; linarith [Real.log_le_log hd0 hltd.le]
  have hc0 : 0 < c := lt_of_lt_of_le ha hac
  have hflrc : 0 < (Real.log (c / (2 * Real.pi)) - (4 / c ^ (2 : ℕ) + Real.pi / c)) / 2 :=
    lt_of_lt_of_le hflr (winding_floor_expr_mono ha hac)
  have hcρ : |c - τc| ≤ ρmax :=
    abs_sub_le_of_mem_Icc_endpoints hρa hρb ⟨hac, le_trans hcd hdb⟩
  have hdρ : |d - τc| ≤ ρmax :=
    abs_sub_le_of_mem_Icc_endpoints hρa hρb ⟨le_trans hac hcd, hdb⟩
  have hsegcd : ∀ τ ∈ Set.Icc c d, linePt τ ∈ ball (linePt τc) R :=
    fun τ hτ => hseg τ ⟨le_trans hac hτ.1, le_trans hτ.2 hdb⟩
  have hpref : 2 * |c - τc| / (R - |c - τc|) + 2 * |d - τc| / (R - |d - τc|) ≤
      4 * ρmax / (R - ρmax) := by
    have h1 := prefactor_mono hR0 hcρ hρR
    have h2 := prefactor_mono hR0 hdρ hρR
    have h3 : 2 * ρmax / (R - ρmax) + 2 * ρmax / (R - ρmax) = 4 * ρmax / (R - ρmax) := by ring
    linarith
  have hρmax0 : 0 ≤ ρmax := le_trans (abs_nonneg _) hρa
  have hρden0 : 0 < R - ρmax := by linarith
  have hnum2nn : 0 ≤ Real.pi + 4 * ρmax / (R - ρmax) * L := by
    have : 0 ≤ 4 * ρmax / (R - ρmax) * L := by positivity
    linarith [Real.pi_pos]
  have hnum :
      Real.pi + (2 * |c - τc| / (R - |c - τc|) + 2 * |d - τc| / (R - |d - τc|)) * L ≤
      Real.pi + 4 * ρmax / (R - ρmax) * L :=
    by nlinarith [mul_le_mul_of_nonneg_right hpref hL0]
  have hden : (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2 ≤
      (Real.log (c / (2 * Real.pi)) - (4 / c ^ (2 : ℕ) + Real.pi / c)) / 2 :=
    winding_floor_expr_mono ha hac
  have hRHSle :
      (Real.pi + (2 * |c - τc| / (R - |c - τc|) + 2 * |d - τc| / (R - |d - τc|)) * L) /
        ((Real.log (c / (2 * Real.pi)) - (4 / c ^ (2 : ℕ) + Real.pi / c)) / 2) ≤
      (Real.pi + 4 * ρmax / (R - ρmax) * L) /
        ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2) := by
    rw [div_le_div_iff₀ hflrc hflr]
    have hp1 := mul_le_mul_of_nonneg_right hnum hflr.le
    have hp2 := mul_le_mul_of_nonneg_left hden hnum2nn
    nlinarith [hp1, hp2]
  have hlongcd' :
      (Real.pi + (2 * |c - τc| / (R - |c - τc|) + 2 * |d - τc| / (R - |d - τc|)) *
          (Real.log Md - Real.log ‖dslope (gN N) ρ' (linePt τc)‖)) /
        ((Real.log (c / (2 * Real.pi)) - (4 / c ^ (2 : ℕ) + Real.pi / c)) / 2) < d - c := by
    rw [← hL_def]; linarith [hRHSle, hlongcd]
  exact seam_edge_forced_online_zero_one_zero N hR0 hc0 hflrc hd_an hd_ne hfact hMd hltd
    hcd hsegcd hlongcd'

/-! ### §5 From an oscillation scale to a crossing count -/

/-- A real function has at least `n` strictly ordered zeros on `[a,b]` once no zero-free
sub-stretch is longer than `Λ` and the segment is longer than `n·Λ`.  Construction: cut `[a,b]`
into `n` sub-intervals each of length `(b−a)/n − η > Λ` and small mutual gaps; each carries a
zero, and the gaps keep the chosen zeros strictly increasing. -/
theorem exists_strictMono_zeros_of_no_long_gap {g : ℝ → ℝ} {a b Λ : ℝ} {n : ℕ}
    (hn : 0 < n) (hΛ : 0 < Λ)
    (hgap : ∀ c d, a ≤ c → c ≤ d → d ≤ b → Λ < d - c → ∃ τ ∈ Set.Icc c d, g τ = 0)
    (hlong : (n : ℝ) * Λ < b - a) :
    ∃ z : Fin n → ℝ, StrictMono z ∧ (∀ i, z i ∈ Set.Icc a b) ∧ (∀ i, g (z i) = 0) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set δ : ℝ := (b - a) / n with hδ_def
  have hδΛ : Λ < δ := by rw [hδ_def, lt_div_iff₀ hn0]; linarith [hlong]
  have hδ0 : 0 < δ := lt_trans hΛ hδΛ
  set η : ℝ := (δ - Λ) / 2 with hη_def
  have hη0 : 0 < η := by rw [hη_def]; linarith
  have hdmc : Λ < δ - η := by rw [hη_def]; linarith
  have hnδ : (n : ℝ) * δ = b - a := by rw [hδ_def]; field_simp
  have hex : ∀ k : Fin n, ∃ τ ∈ Set.Icc (a + (k.val : ℝ) * δ)
      (a + (k.val : ℝ) * δ + (δ - η)), g τ = 0 := by
    intro k
    have hk1 : ((k.val : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt k.isLt
    have hknn : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
    refine hgap _ _ ?_ ?_ ?_ ?_
    · nlinarith [hknn, hδ0.le]
    · linarith [hdmc, hΛ]
    · have heq : (a + (k.val : ℝ) * δ + (δ - η)) = a + ((k.val : ℝ) + 1) * δ - η := by ring
      rw [heq]
      have hstep : ((k.val : ℝ) + 1) * δ ≤ (n : ℝ) * δ :=
        mul_le_mul_of_nonneg_right hk1 hδ0.le
      rw [hnδ] at hstep
      linarith [hη0]
    · linarith [hdmc]
  refine ⟨fun k => (hex k).choose, ?_, ?_, ?_⟩
  · intro i j hij
    have hi := (hex i).choose_spec.1
    have hj := (hex j).choose_spec.1
    rw [Set.mem_Icc] at hi hj
    have hval : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.mp hij)
    have hchain : a + (i.val : ℝ) * δ + (δ - η) ≤ a + (j.val : ℝ) * δ - η := by
      nlinarith [mul_le_mul_of_nonneg_right hval hδ0.le]
    linarith [hi.2, hj.1, hchain, hη0]
  · intro k
    have hk := (hex k).choose_spec.1
    rw [Set.mem_Icc] at hk ⊢
    have hk1 : ((k.val : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt k.isLt
    have hknn : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
    have hstep : ((k.val : ℝ) + 1) * δ ≤ (n : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hk1 hδ0.le
    rw [hnδ] at hstep
    exact ⟨by nlinarith [hk.1, hknn, hδ0.le], by nlinarith [hk.2, hstep, hη0]⟩
  · intro k
    exact (hex k).choose_spec.2

/-- The seam carries no crossing-free stretch longer than `Λ` on `[A,B]`: every sub-stretch
longer than `Λ` contains an on-line real-part zero of the completed truncation.  This is the
uniform oscillation-scale datum a whole seam segment supplies; `§4` produces it on a single
one-zero disc window, and a disc covering of a long segment supplies it globally. -/
def SeamNoQuietStretch (N : ℕ) (A B Λ : ℝ) : Prop :=
  ∀ c d, A ≤ c → c ≤ d → d ≤ B → Λ < d - c →
    ∃ τ ∈ Set.Icc c d, (completedGN N (linePt τ)).re = 0

/-- A one-zero disc window supplies the seam oscillation-scale datum on that window, at scale
`Λ = (π + (4ρmax/(R − ρmax))·(log Md − log‖dslope center‖))/windingFloor(a)`. -/
theorem seamNoQuietStretch_of_disc_one_zero (N : ℕ)
    {τc a b R Md ρmax : ℝ} {ρ' : ℂ} (hR0 : 0 < R) (ha : 0 < a)
    (hflr : 0 < (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
    (hd_an : AnalyticOnNhd ℂ (dslope (gN N) ρ') (ball (linePt τc) R))
    (hd_ne : ∀ z ∈ ball (linePt τc) R, dslope (gN N) ρ' z ≠ 0)
    (hfact : ∀ z ∈ ball (linePt τc) R, gN N z = (z - ρ') * dslope (gN N) ρ' z)
    (hMd : ∀ z ∈ ball (linePt τc) R, ‖dslope (gN N) ρ' z‖ ≤ Md)
    (hltd : ‖dslope (gN N) ρ' (linePt τc)‖ < Md)
    (hρa : |a - τc| ≤ ρmax) (hρb : |b - τc| ≤ ρmax) (hρR : ρmax < R)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R) :
    SeamNoQuietStretch N a b
      ((Real.pi + 4 * ρmax / (R - ρmax) *
          (Real.log Md - Real.log ‖dslope (gN N) ρ' (linePt τc)‖)) /
        ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)) :=
  seam_no_long_sign_constant_stretch_one_zero N hR0 ha hflr hd_an hd_ne hfact hMd hltd
    hρa hρb hρR hseg

/-- **Crossing count from the oscillation scale.**  A seam segment on which no crossing-free
stretch exceeds `Λ`, with total length exceeding `n·Λ`, carries at least `n` strictly ordered
on-line carrier zeros.  Since the one-zero oscillation scale is `Λ ≍ 1/windingFloor ≍ 1/log T`,
a segment of fixed length carries `≳ (B − A)·log T` crossings: the seam oscillates at the
`1/log T` scale. -/
theorem seam_crossing_count_of_no_quiet_stretch {N : ℕ} {A B Λ : ℝ} {n : ℕ}
    (h : SeamNoQuietStretch N A B Λ) (hΛ : 0 < Λ) (hn : 0 < n)
    (hlong : (n : ℝ) * Λ < B - A) :
    ∃ z : Fin n → ℝ, StrictMono z ∧ (∀ i, z i ∈ Set.Icc A B) ∧
      (∀ i, gN N (linePt (z i)) = 0) := by
  obtain ⟨z, hmono, hmem, hzero⟩ :=
    exists_strictMono_zeros_of_no_long_gap (g := fun τ => (completedGN N (linePt τ)).re)
      hn hΛ h hlong
  exact ⟨z, hmono, hmem, fun i => gN_line_eq_zero_of_completedGN_re_eq_zero (hzero i)⟩

/-- **One-zero-disc crossing count, with the oscillation interface discharged.**
A critical-line window contained in a one-zero carrier disc carries at least `n` strictly
ordered on-line carrier zeros once its length exceeds `n` times the explicit
Borel--Carathéodory/winding scale.  The conclusion consumes only the concrete analytic disc
data; the intermediate `SeamNoQuietStretch` predicate is constructed internally. -/
theorem seam_crossing_count_of_disc_one_zero (N : ℕ)
    {τc a b R Md ρmax : ℝ} {ρ' : ℂ} {n : ℕ} (hR0 : 0 < R) (ha : 0 < a)
    (hflr : 0 < (Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)
    (hd_an : AnalyticOnNhd ℂ (dslope (gN N) ρ') (ball (linePt τc) R))
    (hd_ne : ∀ z ∈ ball (linePt τc) R, dslope (gN N) ρ' z ≠ 0)
    (hfact : ∀ z ∈ ball (linePt τc) R, gN N z = (z - ρ') * dslope (gN N) ρ' z)
    (hMd : ∀ z ∈ ball (linePt τc) R, ‖dslope (gN N) ρ' z‖ ≤ Md)
    (hltd : ‖dslope (gN N) ρ' (linePt τc)‖ < Md)
    (hρa : |a - τc| ≤ ρmax) (hρb : |b - τc| ≤ ρmax) (hρR : ρmax < R)
    (hseg : ∀ τ ∈ Set.Icc a b, linePt τ ∈ ball (linePt τc) R)
    (hΛ : 0 <
      (Real.pi + 4 * ρmax / (R - ρmax) *
          (Real.log Md - Real.log ‖dslope (gN N) ρ' (linePt τc)‖)) /
        ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2))
    (hn : 0 < n)
    (hlong :
      (n : ℝ) *
          ((Real.pi + 4 * ρmax / (R - ρmax) *
              (Real.log Md - Real.log ‖dslope (gN N) ρ' (linePt τc)‖)) /
            ((Real.log (a / (2 * Real.pi)) - (4 / a ^ (2 : ℕ) + Real.pi / a)) / 2)) <
        b - a) :
    ∃ z : Fin n → ℝ, StrictMono z ∧ (∀ i, z i ∈ Set.Icc a b) ∧
      (∀ i, gN N (linePt (z i)) = 0) :=
  seam_crossing_count_of_no_quiet_stretch
    (seamNoQuietStretch_of_disc_one_zero N hR0 ha hflr hd_an hd_ne hfact hMd hltd
      hρa hρb hρR hseg)
    hΛ hn hlong

/-- Zeros carried by pairwise strictly separated sub-intervals are strictly ordered: choosing
one zero from each of `n` slots `[lo k, hi k]` with `hi i < lo j` for `i < j` gives an
increasing family. -/
theorem exists_strictMono_zeros_of_slot_zeros {g : ℝ → ℝ} {A B : ℝ} {n : ℕ}
    (lo hi : Fin n → ℝ)
    (hbnd : ∀ k, A ≤ lo k ∧ hi k ≤ B)
    (hsep : ∀ i j : Fin n, i < j → hi i < lo j)
    (hzero : ∀ k, ∃ τ ∈ Set.Icc (lo k) (hi k), g τ = 0) :
    ∃ z : Fin n → ℝ, StrictMono z ∧ (∀ i, z i ∈ Set.Icc A B) ∧ (∀ i, g (z i) = 0) := by
  refine ⟨fun k => (hzero k).choose, ?_, ?_, ?_⟩
  · intro i j hij
    have hi := (hzero i).choose_spec.1
    have hj := (hzero j).choose_spec.1
    rw [Set.mem_Icc] at hi hj
    exact lt_of_le_of_lt hi.2 (lt_of_lt_of_le (hsep i j hij) hj.1)
  · intro k
    have hk := (hzero k).choose_spec.1
    rw [Set.mem_Icc] at hk ⊢
    exact ⟨le_trans (hbnd k).1 hk.1, le_trans hk.2 (hbnd k).2⟩
  · intro k
    exact (hzero k).choose_spec.2

/-- **Crossing count from disjoint forced boxes.**  If `n` pairwise strictly separated sub-boxes
of a seam segment each force an on-line carrier crossing (each by its own one-zero disc via
`seam_edge_forced_crossing_one_zero`), the segment carries at least `n` strictly ordered on-line
carrier zeros.  This is the non-degenerate crossing count: distinct boxes contribute distinct
zeros, so the tally grows with the number of forced boxes. -/
theorem seam_crossing_count_of_slots {N : ℕ} {A B : ℝ} {n : ℕ}
    (lo hi : Fin n → ℝ)
    (hbnd : ∀ k, A ≤ lo k ∧ hi k ≤ B)
    (hsep : ∀ i j : Fin n, i < j → hi i < lo j)
    (hzero : ∀ k, ∃ τ ∈ Set.Icc (lo k) (hi k), gN N (linePt τ) = 0) :
    ∃ z : Fin n → ℝ, StrictMono z ∧ (∀ i, z i ∈ Set.Icc A B) ∧
      (∀ i, gN N (linePt (z i)) = 0) := by
  have hzero' : ∀ k, ∃ τ ∈ Set.Icc (lo k) (hi k), (completedGN N (linePt τ)).re = 0 :=
    fun k => by
      obtain ⟨τ, hτ, hz⟩ := hzero k
      exact ⟨τ, hτ, completedGN_re_eq_zero_of_gN_line_eq_zero hz⟩
  obtain ⟨z, hmono, hmem, hz⟩ :=
    exists_strictMono_zeros_of_slot_zeros (g := fun τ => (completedGN N (linePt τ)).re)
      lo hi hbnd hsep hzero'
  exact ⟨z, hmono, hmem, fun i => gN_line_eq_zero_of_completedGN_re_eq_zero (hz i)⟩

end RHTower
