/-
The length-sensitive seam crossing tower, and where the seam-positivity program meets RH.

The one-step cutoff crossing `Δ_p = (1 − Q_p)S_p Q_p` is a rank-one seam.  Its length-graded
refinement is the `r`-step crossing `B_{p,r} = (1 − Q_p)S_p^r Q_p`, which sends the shell `e_n`
(`|ξ|_p = p^n`) to `e_{n−r}` for `1 ≤ n ≤ r` and to `0` otherwise — it crosses exactly `r` shells.

* **Crossing-energy law** (`crossHS_inner`).  In the shell basis, `B_{p,r}` has nonzero (unit) matrix
  entries exactly at the `r` positions `{(n−r, n) : 1 ≤ n ≤ r}` (`crossSupport`), so its
  Hilbert–Schmidt self-energy is `‖B_{p,r}‖²_HS = r` (`crossSupport_card`) and distinct crossings are
  orthogonal (`crossSupport_orthogonal`): `⟨B_{p,r}, B_{p,s}⟩_HS = r·δ_{r,s}`.  The prime-power weight
  `1/r` in `log(1 − p^(−s))⁻¹ = Σ_r p^(−rs)/r` is the reciprocal of the `r`-shell crossing energy.

* **Reproducing kernel = Euler factor** (`expKernel_eq_eulerFactor`).  The reproducing kernel of the
  seam Dirichlet space, evaluated at the boundary point `p^(−s)`, exponentiates to the local Euler
  factor: `exp(Σ_r (p^(−s))^r / r) = (1 − p^(−s))⁻¹`.  The Euler factor is the exponential of the
  crossing kernel, not merely a rank-one determinant.

* **Finite-prime Weil energy** (`finite_weil_energy_nonneg`).  Weighting each `r`-crossing by a test
  value gives the manifestly nonnegative finite energy `Σ_{p,r} r·‖h(r log p)‖²` — the finite-prime
  half of a Weil-type form, positive because each crossing contributes its energy `r ≥ 0`.

The seam-positivity program proposes to complete this into a self-dual seam Hilbert space on which a
scaling generator `Θ_Δ` is skew-adjoint-after-shift and the determinant identity makes the ξ-zeros its
spectrum — forcing them onto the critical line.  The final two sections formalize that endpoint and
say, mechanically, exactly what it costs.

* **The endpoint implies RH** (`rh_of_seam_spectral`).  If every strip ξ-zero has the self-adjoint
  spectral form `ρ = 1/2 + iλ` (`λ ∈ ℝ`) — the output of a Hilbert–Pólya seam generator — then RH.

* **The endpoint IS RH** (`seam_spectral_iff_rh`).  That hypothesis is *equivalent* to RH.  So the
  remaining ingredient of the program — the self-adjoint spectral identification of the zeros — is not
  a bridge lemma derivable from the crossing tower; discharging it is proving RH.  The crossing tower
  (`§1–§3`) supplies the Euler/energy side on `Re s > 1`; the spectral side lives at the zeros in the
  strip; connecting them across the wall is the whole problem.
-/
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.EulerTruncationRigidity

noncomputable section

namespace RHTower

open Complex Finset

/-! ### §1 The crossing tower and its energy law -/

/-- The Hilbert–Schmidt support of the `r`-step seam crossing `B_{p,r}`: the `r` matrix positions
`{(n − r, n) : 1 ≤ n ≤ r}` where its unit entries sit. -/
def crossSupport (r : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (1 : ℤ) r).image (fun m => (m - r, m))

/-- **The crossing self-energy is the crossing length.**  `B_{p,r}` has exactly `r` unit entries, so
`‖B_{p,r}‖²_HS = r`. -/
theorem crossSupport_card (r : ℕ) : (crossSupport r).card = r := by
  rw [crossSupport, Finset.card_image_of_injective _ (by
    intro a b hab; exact (Prod.ext_iff.mp hab).2), Int.card_Icc]
  simp

/-- **Distinct-length crossings are orthogonal.**  `B_{p,r}` and `B_{p,s}` share no matrix position
when `r ≠ s`, because a common entry would force `n − r = n − s`. -/
theorem crossSupport_orthogonal {r s : ℕ} (h : r ≠ s) : crossSupport r ∩ crossSupport s = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨a, b⟩ hmem
  rw [Finset.mem_inter, crossSupport, crossSupport, Finset.mem_image, Finset.mem_image] at hmem
  obtain ⟨⟨m, _, hmeq⟩, ⟨m', _, hm'eq⟩⟩ := hmem
  have hb : m = b := (Prod.ext_iff.mp hmeq).2
  have hb' : m' = b := (Prod.ext_iff.mp hm'eq).2
  have ha : m - r = a := (Prod.ext_iff.mp hmeq).1
  have ha' : m' - s = a := (Prod.ext_iff.mp hm'eq).1
  apply h; omega

/-- **The crossing-energy law** `⟨B_{p,r}, B_{p,s}⟩_HS = r·δ_{r,s}`.  The Hilbert–Schmidt inner product
of two length crossings (the count of shared unit entries) is the crossing length when the lengths
agree and `0` otherwise. -/
theorem crossHS_inner (r s : ℕ) :
    (crossSupport r ∩ crossSupport s).card = if r = s then r else 0 := by
  by_cases h : r = s
  · subst h; rw [Finset.inter_self, crossSupport_card]; simp
  · rw [crossSupport_orthogonal h, Finset.card_empty, if_neg h]

/-! ### §2 The reproducing kernel is the Euler factor -/

/-- **The Euler factor is the exponential of the seam reproducing kernel.**  The kernel
`K_p(z) = Σ_r z^r / r` evaluated at the boundary point `z = p^(−s)` gives
`exp(Σ_r (p^(−s))^r / r) = (1 − p^(−s))⁻¹` — the local Euler factor, with the `1/r` weight the
reciprocal `r`-crossing energy of `§1`. -/
theorem expKernel_eq_eulerFactor {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    Complex.exp (∑' r : ℕ, ((p : ℂ) ^ (-s)) ^ r / (r : ℂ)) = (1 - (p : ℂ) ^ (-s))⁻¹ := by
  have hsum : (∑' r : ℕ, ((p : ℂ) ^ (-s)) ^ r / (r : ℂ)) = -Complex.log (1 - (p : ℂ) ^ (-s)) :=
    (neg_log_euler_base_hasSum hp hs).tsum_eq
  rw [hsum, Complex.exp_neg, Complex.exp_log (eulerFactor_ne_zero hp hs)]

/-! ### §3 Finite-prime Weil energy is manifestly positive -/

/-- **The finite-prime seam energy is nonnegative.**  Weighting each `(p, r)`-crossing of energy `r`
by a test value `h`, the finite-prime Weil energy `Σ_{(p,r)} r·‖h(p,r)‖²` is `≥ 0`: each crossing
contributes its own nonnegative energy.  This is the finite half of the Weil quadratic form realized
as a Hilbert–Schmidt norm. -/
theorem finite_weil_energy_nonneg (S : Finset (ℕ × ℕ)) (h : ℕ × ℕ → ℂ) :
    0 ≤ ∑ pr ∈ S, (pr.2 : ℝ) * ‖h pr‖ ^ 2 :=
  Finset.sum_nonneg fun pr _ => by positivity

/-! ### §4 The seam-spectral endpoint implies RH -/

/-- **Hilbert–Pólya seam endpoint ⟹ RH.**  If every ξ-zero in the strip has the self-adjoint spectral
form `ρ = 1/2 + iλ` with `λ` real — precisely what a skew-adjoint-after-shift seam generator `Θ_Δ`
would produce via the determinant identity — then the Riemann Hypothesis holds. -/
theorem rh_of_seam_spectral
    (h : ∀ ρ : ℂ, xi ρ = 0 → 0 < ρ.re → ρ.re < 1 → ∃ lam : ℝ, ρ = 1 / 2 + (lam : ℂ) * I) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hxi
  have hre : 1 / 2 < s.re := hs
  have hlt1 : s.re < 1 := by
    by_contra hge
    exact xi_ne_zero_of_one_le_re (not_lt.mp hge) hxi
  obtain ⟨lam, hlam⟩ := h s hxi (by linarith) hlt1
  have hcalc : (1 / 2 + (lam : ℂ) * I).re = 1 / 2 := by simp
  rw [hlam, hcalc] at hre
  linarith

/-! ### §5 The seam-spectral endpoint IS RH — the remaining ingredient is not a bridge lemma -/

/-- **The seam-spectral endpoint is equivalent to RH.**  The hypothesis of `rh_of_seam_spectral` — the
self-adjoint spectral identification of the ξ-zeros — is logically *equivalent* to the Riemann
Hypothesis.  Hence it is not a bridge lemma one could fill from the crossing tower (`§1–§3`): the
crossing tower gives the Euler/energy side on `Re s > 1`, whereas the spectral identification lives at
the zeros in the strip, and connecting them **is** RH.  This is what "let Lean speak" says about the
seam-positivity program: every provable ingredient is on the wrong side of the wall, and the one that
would cross it is the theorem itself. -/
theorem seam_spectral_iff_rh :
    (∀ ρ : ℂ, xi ρ = 0 → 0 < ρ.re → ρ.re < 1 → ∃ lam : ℝ, ρ = 1 / 2 + (lam : ℂ) * I)
      ↔ RiemannHypothesis := by
  refine ⟨rh_of_seam_spectral, ?_⟩
  intro hrh ρ hxi h0 h1
  have hne1 : ρ ≠ 1 := by rintro rfl; norm_num at h1
  have hz : riemannZeta ρ = 0 := (xi_eq_zero_iff h0 hne1).mp hxi
  have hnt : ¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, rfl⟩
    have hcast : (-2 * ((n : ℂ) + 1)).re = -2 * (n + 1) := by simp [Complex.mul_re]
    rw [hcast] at h0
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hline := hrh ρ hz hnt hne1
  refine ⟨ρ.im, ?_⟩
  conv_lhs => rw [← Complex.re_add_im ρ]
  rw [hline]; push_cast; ring

end RHTower
