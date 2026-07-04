/-
Doc 72 §4 + doc 22 §1 + doc 32 §5 (task #143): the CONCRETE carrier — g_N made
unconditional in Lean.

Doc 72's attack-as-false run collapsed the lane's carrier design onto ζ's own
matched truncation: "the parity carrier the lane spent docs 61–71 designing is
g_N — the doc 22 object". This module replaces `AnnealCarrier`'s abstract
hypotheses (a free χ with an assumed χ-identity, a free approximant) by the
ACTUAL objects, with the identities PROVED from mathlib:

* `dirichletPoly` — the finite sum `Σ_{1≤n≤N} n^{−s}`: entire
  (`dirichletPoly_differentiable`), Schwarz-real (`dirichletPoly_conj`).
* `zetaChi` — THE χ of ζ in completed form `Γ_ℝ(1−s)/Γ_ℝ(s)`:
  `zetaChi_mul_one_sub_of_mem_strip` proves the χ-identity χ(s)χ(1−s) = 1
  UNCONDITIONALLY on the open critical strip (`Gammaℝ_ne_zero_of_re_pos`), and
  `zeta_eq_zetaChi_mul` certifies it against ζ's own functional equation
  (`riemannZeta_def_of_ne_zero` + `completedRiemannZeta_one_sub`) — the
  validator that this χ is not a fabrication.
* `gN := chiSymmetrize zetaChi (dirichletPoly N)` — the carrier. Its exact
  asymmetric FE `gN_one_sub`, Schwarz reality `gN_conj`, strip analyticity
  `gN_analyticAt`, and FE order-pairing `gN_orderAt_one_sub` are all proved,
  hypothesis-free on the strip. The abstract `hχ` of `chiSymmetrize_one_sub`
  is DISCHARGED (via the pointwise strengthening `chiSymmetrize_one_sub_at`).
* `completedGN := archFactor · gN` — the finite object on ξ's own layer:
  `completedGN_one_sub` proves the exact EVEN functional equation on the strip
  (the full ξ-shape at finite Euler depth), `completedGN_orderAt_one_sub` its
  order equivariance — exactly what the window identity (ID) of
  `WindowRelation` consumes on the finite side.
* `analyticOrderAt_one_sub` — hypothesis-free strengthening of
  `analyticOrderAt_comp_one_sub` (entirety dropped, via
  `analyticOrderAt_comp_of_deriv_ne_zero`): order equivariance now applies to
  the meromorphic completed carrier.
* `completed_domination_iff` — doc 32 §5's "the domination divides out":
  completed-level domination ⟺ the raw `‖ζ − g_N‖ < ‖g_N‖`, via
  `xi_eq_archFactor_mul_zeta` and `norm_mul_sub_lt_iff`. No archimedean
  bookkeeping survives in the premise.
* `AFEAccurateOn` / `CarrierFloorOn` — the ONLY two analytic residues of the
  whole reduction, as named Prop interfaces: (AFE) accuracy of the truncation
  and (LOW) the carrier floor, per window.
* `anneal_deck_transport` — THE capstone: on a strip window whose charts carry
  the two interfaces, every level-2^k deck reading of ξ equals that of the
  completed concrete truncation. Doc 22's reduction, end to end, on the actual
  objects — conditional on nothing but the two named numerical interfaces.
-/
import GaloisForLFunctions.RHTower.AnnealCarrier
import GaloisForLFunctions.RHTower.SeamTransport

namespace RHTower

open Complex

/-! ### §1 Order equivariance under s ↦ 1 − s, hypothesis-free -/

/-- Vanishing orders are equivariant under `w ↦ 1 − w` — for ANY function
(strengthens `analyticOrderAt_comp_one_sub`, dropping entirety). -/
theorem analyticOrderAt_one_sub (f : ℂ → ℂ) (z : ℂ) :
    analyticOrderAt (fun w => f (1 - w)) (1 - z) = analyticOrderAt f z := by
  have hg : AnalyticAt ℂ (fun w : ℂ => 1 - w) (1 - z) := analyticAt_const.sub analyticAt_id
  have hd : HasDerivAt (fun w : ℂ => 1 - w) (0 - 1) (1 - z) :=
    (hasDerivAt_const (1 - z) 1).sub (hasDerivAt_id (1 - z))
  have hg' : deriv (fun w : ℂ => 1 - w) (1 - z) ≠ 0 := by
    rw [hd.deriv]; norm_num
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := f) hg hg'
  rw [show (1 : ℂ) - (1 - z) = z from by ring] at h
  simpa [Function.comp] using h

/-! ### §2 The concrete truncation -/

/-- The length-`N` Dirichlet polynomial `Σ_{1≤n≤N} n^{−s}`. -/
noncomputable def dirichletPoly (N : ℕ) : ℂ → ℂ := fun s => ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)

private lemma natCast_cpow_conj' (a : ℕ) (s : ℂ) :
    (a : ℂ) ^ ((starRingEnd ℂ) s) = (starRingEnd ℂ) ((a : ℂ) ^ s) := by
  have harg : (a : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg a)]
    exact Ne.symm Real.pi_ne_zero
  have h := Complex.cpow_conj (a : ℂ) s harg
  rwa [map_natCast] at h

theorem dirichletPoly_differentiable (N : ℕ) : Differentiable ℂ (dirichletPoly N) := by
  have h : Differentiable ℂ (∑ n ∈ Finset.Icc 1 N, fun s : ℂ => (n : ℂ) ^ (-s)) := by
    apply Differentiable.sum
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1)
    exact differentiable_id.neg.const_cpow (Or.inl hn0)
  have heq : dirichletPoly N = ∑ n ∈ Finset.Icc 1 N, fun s : ℂ => (n : ℂ) ^ (-s) := by
    funext s
    simp [dirichletPoly]
  rwa [heq]

theorem dirichletPoly_conj (N : ℕ) (s : ℂ) :
    dirichletPoly N ((starRingEnd ℂ) s) = (starRingEnd ℂ) (dirichletPoly N s) := by
  unfold dirichletPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← map_neg, natCast_cpow_conj']

/-! ### §3 The concrete χ of ζ -/

/-- The χ-factor of ζ's asymmetric FE, in completed form: `χ(s) = Γ_ℝ(1−s)/Γ_ℝ(s)`. -/
noncomputable def zetaChi : ℂ → ℂ := fun s => Gammaℝ (1 - s) / Gammaℝ s

theorem zetaChi_mul_one_sub {s : ℂ} (hs : Gammaℝ s ≠ 0) (hs' : Gammaℝ (1 - s) ≠ 0) :
    zetaChi s * zetaChi (1 - s) = 1 := by
  unfold zetaChi
  rw [show (1 : ℂ) - (1 - s) = s from by ring]
  field_simp

/-- On the OPEN CRITICAL STRIP the χ-identity is unconditional. -/
theorem zetaChi_mul_one_sub_of_mem_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    zetaChi s * zetaChi (1 - s) = 1 :=
  zetaChi_mul_one_sub (Gammaℝ_ne_zero_of_re_pos h0)
    (Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.sub_re, Complex.one_re]; linarith))

theorem zetaChi_conj (s : ℂ) :
    zetaChi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (zetaChi s) := by
  unfold zetaChi
  rw [show (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) from by
        rw [map_sub, map_one],
      Gammaℝ_conj, Gammaℝ_conj, map_div₀]

/-- Consistency validator: `zetaChi` is THE χ of ζ — `ζ(s) = χ(s)·ζ(1−s)`. -/
theorem zeta_eq_zetaChi_mul {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hG : Gammaℝ (1 - s) ≠ 0) :
    riemannZeta s = zetaChi s * riemannZeta (1 - s) := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [riemannZeta_def_of_ne_zero h0, riemannZeta_def_of_ne_zero h1s,
    completedRiemannZeta_one_sub]
  unfold zetaChi
  rcases eq_or_ne (Gammaℝ s) 0 with h | h
  · simp [h]
  · field_simp

/-- Γ_ℝ is analytic wherever it is nonvanishing (via the entire reciprocal). -/
theorem Gammaℝ_analyticAt {z : ℂ} (hz : Gammaℝ z ≠ 0) : AnalyticAt ℂ Gammaℝ z := by
  have hinv : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) z :=
    (differentiable_Gammaℝ_inv.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have h := hinv.inv (inv_ne_zero hz)
  have heq : (fun s => (Gammaℝ s)⁻¹)⁻¹ = Gammaℝ := by
    funext s
    rw [Pi.inv_apply, inv_inv]
  rwa [heq] at h

theorem zetaChi_analyticAt {z : ℂ} (hz : Gammaℝ (1 - z) ≠ 0) : AnalyticAt ℂ zetaChi z := by
  have haff : AnalyticAt ℂ (fun s : ℂ => 1 - s) z := analyticAt_const.sub analyticAt_id
  have h1 : AnalyticAt ℂ (fun s : ℂ => Gammaℝ (1 - s)) z := by
    have h := (Gammaℝ_analyticAt hz).comp haff
    simpa [Function.comp] using h
  have h2 : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) z :=
    (differentiable_Gammaℝ_inv.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have h := h1.mul h2
  have heq : zetaChi = fun s => Gammaℝ (1 - s) * (Gammaℝ s)⁻¹ := by
    funext s
    rw [zetaChi, div_eq_mul_inv]
  rwa [heq]

/-! ### §4 Pointwise χ-symmetrization FE -/

/-- Pointwise strengthening of `chiSymmetrize_one_sub`: the exact asymmetric FE at `s`
needs the χ-identity at `s` only. -/
theorem chiSymmetrize_one_sub_at {χ h : ℂ → ℂ} {s : ℂ} (hχ : χ s * χ (1 - s) = 1) :
    chiSymmetrize χ h (1 - s) = χ (1 - s) * chiSymmetrize χ h s := by
  unfold chiSymmetrize
  rw [show (1 : ℂ) - (1 - s) = s from by ring]
  linear_combination (-(h (1 - s))) * hχ

/-! ### §5 THE carrier -/

/-- The Riemann–Siegel-type carrier: `g_N = h_N + χ·h_N(1−·)` (doc 22 §1; doc 72 §4:
"the parity carrier IS g_N"). -/
noncomputable def gN (N : ℕ) : ℂ → ℂ := chiSymmetrize zetaChi (dirichletPoly N)

/-- The exact asymmetric FE of the concrete carrier — UNCONDITIONAL on the strip. -/
theorem gN_one_sub {N : ℕ} {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    gN N (1 - s) = zetaChi (1 - s) * gN N s :=
  chiSymmetrize_one_sub_at (zetaChi_mul_one_sub_of_mem_strip h0 h1)

/-- Schwarz reality of the concrete carrier. -/
theorem gN_conj (N : ℕ) (s : ℂ) :
    gN N ((starRingEnd ℂ) s) = (starRingEnd ℂ) (gN N s) := by
  unfold gN chiSymmetrize
  rw [show (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) from by
        rw [map_sub, map_one],
      dirichletPoly_conj, dirichletPoly_conj, zetaChi_conj, map_add, map_mul]

theorem gN_analyticAt {N : ℕ} {z : ℂ} (hz : Gammaℝ (1 - z) ≠ 0) :
    AnalyticAt ℂ (gN N) z := by
  have hpoly : AnalyticAt ℂ (dirichletPoly N) z :=
    ((dirichletPoly_differentiable N).differentiableOn.analyticOnNhd isOpen_univ) z
      (Set.mem_univ z)
  have haff : AnalyticAt ℂ (fun s : ℂ => 1 - s) z := analyticAt_const.sub analyticAt_id
  have hpoly' : AnalyticAt ℂ (fun s : ℂ => dirichletPoly N (1 - s)) z := by
    have h := (((dirichletPoly_differentiable N).differentiableOn.analyticOnNhd
      isOpen_univ) (1 - z) (Set.mem_univ _)).comp haff
    simpa [Function.comp] using h
  have h := hpoly.add ((zetaChi_analyticAt hz).mul hpoly')
  exact h

/-- FE pairing of vanishing orders for the concrete carrier, on the strip. -/
theorem gN_orderAt_one_sub {N : ℕ} {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderAt (gN N) (1 - z) = analyticOrderAt (gN N) z := by
  have h0' : 0 < (1 - z).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have h1' : (1 - z).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hmem : {w : ℂ | 0 < w.re ∧ w.re < 1} ∈ nhds (1 - z) := hopen.mem_nhds ⟨h0', h1'⟩
  have hev : gN N =ᶠ[nhds (1 - z)] fun w => zetaChi w * gN N (1 - w) := by
    filter_upwards [hmem] with w hw
    have hw0 : 0 < (1 - w).re := by simp only [Complex.sub_re, Complex.one_re]; linarith [hw.2]
    have hw1 : (1 - w).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith [hw.1]
    have h := gN_one_sub (N := N) hw0 hw1
    rw [show (1 : ℂ) - (1 - w) = w from by ring] at h
    exact h
  have hGz : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hG1z : Gammaℝ (1 - z) ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0'
  have hχa : AnalyticAt ℂ zetaChi (1 - z) := by
    apply zetaChi_analyticAt
    rw [show (1 : ℂ) - (1 - z) = z from by ring]
    exact hGz
  have hga : AnalyticAt ℂ (fun w : ℂ => gN N (1 - w)) (1 - z) := by
    have haff : AnalyticAt ℂ (fun w : ℂ => 1 - w) (1 - z) := analyticAt_const.sub analyticAt_id
    have hg : AnalyticAt ℂ (gN N) ((fun w : ℂ => 1 - w) (1 - z)) := by
      simpa [show (1 : ℂ) - (1 - z) = z from by ring] using gN_analyticAt (N := N) hG1z
    have h := hg.comp haff
    simpa [Function.comp] using h
  have hmul : (fun w : ℂ => zetaChi w * gN N (1 - w))
      = zetaChi * fun w : ℂ => gN N (1 - w) := rfl
  rw [analyticOrderAt_congr hev, hmul, analyticOrderAt_mul hχa hga]
  have hχ0 : analyticOrderAt zetaChi (1 - z) = 0 := by
    rw [analyticOrderAt_eq_zero]
    right
    unfold zetaChi
    rw [show (1 : ℂ) - (1 - z) = z from by ring]
    exact div_ne_zero hGz hG1z
  rw [hχ0, zero_add, analyticOrderAt_one_sub]

/-! ### §6 The completed carrier and the ξ bridge -/

/-- The archimedean dressing of ξ: `s(s−1)/2 · Γ_ℝ(s)`. -/
noncomputable def archFactor : ℂ → ℂ := fun s => s * (s - 1) / 2 * Gammaℝ s

theorem archFactor_ne_zero {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) :
    archFactor s ≠ 0 :=
  mul_ne_zero (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero) hG

/-- ξ in raw-times-dressing form: `ξ = archFactor · ζ` off the poles. -/
theorem xi_eq_archFactor_mul_zeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) :
    xi s = archFactor s * riemannZeta s := by
  rw [xi_eq_half_mul h0 h1, riemannZeta_def_of_ne_zero h0]
  unfold archFactor
  field_simp

/-- The completed concrete carrier `Φ̃_N = archFactor · g_N` — the finite object on
ξ's own layer. -/
noncomputable def completedGN (N : ℕ) : ℂ → ℂ := fun s => archFactor s * gN N s

/-- The completed carrier satisfies the exact EVEN functional equation on the strip
— unconditionally: the full ξ-shape at finite Euler depth. -/
theorem completedGN_one_sub {N : ℕ} {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    completedGN N (1 - s) = completedGN N s := by
  have hG1 : Gammaℝ (1 - s) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  unfold completedGN archFactor
  rw [gN_one_sub h0 h1]
  unfold zetaChi
  rw [show (1 : ℂ) - (1 - s) = s from by ring]
  field_simp
  ring

/-- Schwarz reality of the completed carrier. -/
theorem completedGN_conj (N : ℕ) (s : ℂ) :
    completedGN N ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedGN N s) := by
  unfold completedGN archFactor
  rw [Gammaℝ_conj, gN_conj, map_mul, map_mul, map_div₀, map_mul, map_sub, map_one,
    map_ofNat]

/-- FE pairing of vanishing orders for the completed carrier, on the strip —
the exact input the window identity (ID) consumes on the finite side. -/
theorem completedGN_orderAt_one_sub {N : ℕ} {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderAt (completedGN N) (1 - z) = analyticOrderAt (completedGN N) z := by
  have h0' : 0 < (1 - z).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have h1' : (1 - z).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hmem : {w : ℂ | 0 < w.re ∧ w.re < 1} ∈ nhds (1 - z) := hopen.mem_nhds ⟨h0', h1'⟩
  have hev : completedGN N =ᶠ[nhds (1 - z)] fun w => completedGN N (1 - w) := by
    filter_upwards [hmem] with w hw
    exact (completedGN_one_sub hw.1 hw.2).symm
  rw [analyticOrderAt_congr hev, analyticOrderAt_one_sub]

/-- The domination bridge: `ξ − Φ̃_N = archFactor · (ζ − g_N)`. -/
theorem xi_sub_completedGN {N : ℕ} {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) :
    xi s - completedGN N s = archFactor s * (riemannZeta s - gN N s) := by
  rw [xi_eq_archFactor_mul_zeta h0 h1 hG]
  unfold completedGN
  ring

/-- Strict domination is invariant under a common nonvanishing factor. -/
theorem norm_mul_sub_lt_iff {u f g : ℂ} (hu : u ≠ 0) :
    ‖u * f - u * g‖ < ‖u * g‖ ↔ ‖f - g‖ < ‖g‖ := by
  rw [← mul_sub, norm_mul, norm_mul]
  exact mul_lt_mul_iff_of_pos_left (norm_pos_iff.mpr hu)

/-- (doc 32 §5) The archimedean factor divides out: completed-level domination
`‖ξ − Φ̃_N‖ < ‖Φ̃_N‖` is EQUIVALENT to the raw inequality `‖ζ − g_N‖ < ‖g_N‖`. -/
theorem completed_domination_iff {N : ℕ} {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) :
    (‖xi s - completedGN N s‖ < ‖completedGN N s‖)
      ↔ (‖riemannZeta s - gN N s‖ < ‖gN N s‖) := by
  rw [xi_sub_completedGN h0 h1 hG]
  unfold completedGN
  rw [norm_mul, norm_mul]
  exact mul_lt_mul_iff_of_pos_left (norm_pos_iff.mpr (archFactor_ne_zero h0 h1 hG))

/-! ### §7 The two named analytic residues and the assembly -/

/-- (AFE) interface: the truncation approximates ζ to accuracy ε on `S`. -/
def AFEAccurateOn (S : Set ℂ) (N : ℕ) (ε : ℝ) : Prop :=
  ∀ z ∈ S, ‖riemannZeta z - gN N z‖ ≤ ε

/-- (LOW) interface: the carrier stays above the floor ε on `S`. -/
def CarrierFloorOn (S : Set ℂ) (N : ℕ) (ε : ℝ) : Prop :=
  ∀ z ∈ S, ε < ‖gN N z‖

/-- Raw domination from the two interfaces. -/
theorem raw_domination_of_interfaces {S : Set ℂ} {N : ℕ} {ε : ℝ}
    (hA : AFEAccurateOn S N ε) (hF : CarrierFloorOn S N ε) :
    ∀ z ∈ S, ‖riemannZeta z - gN N z‖ < ‖gN N z‖ := fun z hz =>
  lt_of_le_of_lt (hA z hz) (hF z hz)

/-- Completed domination from the two interfaces, on strip subsets — exactly the
`hdom` premise of `seam_transport`. -/
theorem completed_domination_of_interfaces {S : Set ℂ} {N : ℕ} {ε : ℝ}
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1)
    (hA : AFEAccurateOn S N ε) (hF : CarrierFloorOn S N ε) :
    ∀ z ∈ S, ‖xi z - completedGN N z‖ < ‖completedGN N z‖ := by
  intro z hz
  obtain ⟨h0r, h1r⟩ := hstrip z hz
  have h0 : z ≠ 0 := by
    rintro rfl
    simp at h0r
  have h1 : z ≠ 1 := by
    rintro rfl
    simp at h1r
  exact (completed_domination_iff h0 h1 (Gammaℝ_ne_zero_of_re_pos h0r)).mpr
    (raw_domination_of_interfaces hA hF z hz)

/-- **The ANNEAL reduction on the concrete carrier** (doc 22 + doc 32 + doc 72 §4):
on a strip window whose charts carry the (AFE) accuracy and (LOW) floor interfaces,
every level-`2^k` deck reading of ξ equals that of the completed finite truncation
`Φ̃_N`. The ONLY analytic content left is the two named interfaces. -/
theorem anneal_deck_transport {N : ℕ} {F₁ F₂ G₁ G₂ : ℂ → ℂ} {a : ℂ} {R : ℝ} {ε : ℝ}
    (k : ℕ) (hR : 0 < R)
    (hstrip : ∀ z ∈ chartR a R ∪ chartL a R, 0 < z.re ∧ z.re < 1)
    (hA : AFEAccurateOn (chartR a R ∪ chartL a R) N ε)
    (hF : CarrierFloorOn (chartR a R ∪ chartL a R) N ε)
    (hF₁ : AnalyticOnNhd ℂ F₁ (chartR a R)) (hF₂ : AnalyticOnNhd ℂ F₂ (chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpF₁ : ∀ z ∈ chartR a R, F₁ z ^ 2 ^ k = xi z)
    (hpF₂ : ∀ z ∈ chartL a R, F₂ z ^ 2 ^ k = xi z)
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ 2 ^ k = completedGN N z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ 2 ^ k = completedGN N z) :
    deckClass F₁ F₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
      deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) :=
  seam_transport_ladder k hR (xi_analyticOnNhd _) hF₁ hF₂ hG₁ hG₂ hpF₁ hpF₂ hpG₁ hpG₂
    (completed_domination_of_interfaces hstrip hA hF)

end RHTower
