/-
# Is the {i,−i}-type deposit compatible with ξ's germ? — the central-parity verdict

The half-charge conservation law (Phase E) says an odd half charge that leaves the upper half must
deposit an even seam order.  Does ξ's actual germ on the seam admit this deposit, or does the
Phase-C central-parity evenness obstruct it?  The geometry answers it.

The `u`-plane seam `{Im u = 0}` splits into three regions with different behaviour:

* `u > 0` : `s = 1/2 + √u` real `> 1/2`, the far-field drain (ξ zero-free);
* `u = 0` : the FE fixed point `s = 1/2`, where central parity lives;
* `u < 0` : `s = 1/2 + i√|u|`, **the critical line** — the on-line ξ-zeros.

An off-line conjugate pair `{u₀, ū₀}` colliding onto the seam lands at `u < 0` (as `β → 1/2` sends
`u₀ = (β − 1/2 + iγ)² → −γ² < 0`), i.e. on the critical line — **not** at the center.

* Off-center (`s ≠ 1/2`) the descent is a local isomorphism, so the seam multiplicity is exactly the
  on-line ξ-order, with **no parity constraint** (`analyticOrderAt_xiDescent_sq_of_ne_center`,
  `xiDescent_online_seam_order`): the descended point sits on the negative-real seam and carries
  `ord_ρ ξ`, which can be odd (all known on-line zeros are simple).
* At the center the descent is ramified: `ord_{1/2} ξ = 2·ord_0(xiDescent)`
  (`xi_central_order_eq_two_mul`) — the central evenness (Phase C) is the descent's halving, satisfied
  for *any* descended order, so a center deposit of xiDescent-order `n` is a central ξ-zero of order
  `2n`, always Phase-C-consistent.
* Under any admissible deformation the seam order changes by an even amount, so the mod-2 seam parity
  — the central-parity constraint — is conserved (`seamOrder_parity_conserved`): the deposit can
  never *violate* central parity.

**Verdict.** Central parity constrains only `u = 0`, and even there it is automatic; the deposit lands
on the critical line `u < 0` where the seam carries arbitrary order.  The deposit is even and preserves
the seam parity.  So **central parity does not obstruct the deposit — it survives.**  The obstruction,
if any, must be finer than parity: it must distinguish a genuine on-line zero from a deposited
pair-collision residue.
-/
import GaloisForLFunctions.RHTower.HalfChargeConservation
import GaloisForLFunctions.RHTower.ReflectionParity

namespace RHTower

open Complex

/-! ### §1 Off-center seam multiplicity: the descent is a local isomorphism away from `1/2` -/

/-- **The descent preserves multiplicity off the center.**  For any `s ≠ 1/2`, the descended point
`(s − 1/2)²` carries exactly the ξ-order at `s`.  (Only `rightHalf` was used in the analogous
`analyticOrderAt_xiDescent_center_sq`, and only to get `s − 1/2 ≠ 0`.) -/
theorem analyticOrderAt_xiDescent_sq_of_ne_center {s : ℂ} (hs : s ≠ (1 / 2 : ℂ)) :
    analyticOrderAt xiDescent ((s - (1 / 2 : ℂ)) ^ (2 : ℕ)) = analyticOrderAt xi s := by
  let φ : ℂ → ℂ := fun z => (z - (1 / 2 : ℂ)) ^ (2 : ℕ)
  have hφ : AnalyticAt ℂ φ s := (analyticAt_id.sub analyticAt_const).pow 2
  have hsne : s - (1 / 2 : ℂ) ≠ 0 := sub_ne_zero.mpr hs
  have hbase : HasDerivAt (fun z : ℂ => z - (1 / 2 : ℂ)) 1 s :=
    (hasDerivAt_id s).sub_const (1 / 2 : ℂ)
  have hderiv_at : HasDerivAt φ (2 * (s - (1 / 2 : ℂ))) s := by
    simpa [φ] using! hbase.pow 2
  have hφ' : deriv φ s ≠ 0 := by
    rw [hderiv_at.deriv]; exact mul_ne_zero two_ne_zero hsne
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := xiDescent) hφ hφ'
  have hxi_ev : xi =ᶠ[nhds s] xiDescent ∘ φ := by
    filter_upwards with z; exact xi_eq_xiDescent z
  rw [analyticOrderAt_congr hxi_ev]
  simpa [φ, Function.comp] using hcomp.symm

/-! ### §2 On-line zeros land on the negative-real seam with preserved (unconstrained) order -/

/-- **On-line ξ-zeros map to the seam.**  For an on-line point `ρ` (`Re ρ = 1/2`, `ρ ≠ 1/2`), the
descended point `(ρ − 1/2)²` lies on the negative-real seam (`Im = 0`, `Re ≤ 0`) and carries exactly
`ord_ρ ξ` — no parity is forced there.  So a seam deposit landing at `u < 0` is order-compatible with
ξ's genuine on-line divisor. -/
theorem xiDescent_online_seam_order {ρ : ℂ} (hre : ρ.re = 1 / 2) (hne : ρ ≠ (1 / 2 : ℂ)) :
    analyticOrderAt xiDescent ((ρ - (1 / 2 : ℂ)) ^ (2 : ℕ)) = analyticOrderAt xi ρ ∧
      ((ρ - (1 / 2 : ℂ)) ^ (2 : ℕ)).im = 0 ∧ ((ρ - (1 / 2 : ℂ)) ^ (2 : ℕ)).re ≤ 0 := by
  have hreps : (ρ - (1 / 2 : ℂ)).re = 0 := by
    rw [Complex.sub_re, hre, show (1 / 2 : ℂ).re = (1 / 2 : ℝ) from by norm_num]; norm_num
  refine ⟨analyticOrderAt_xiDescent_sq_of_ne_center hne, ?_, ?_⟩
  · rw [pow_two, Complex.mul_im, hreps]; ring
  · rw [pow_two, Complex.mul_re, hreps]; nlinarith [mul_self_nonneg (ρ - (1 / 2 : ℂ)).im]

/-! ### §3 The center relation: central parity is the descent's halving (Phase C) -/

/-- **The central order doubles under the descent.**  `ord_{1/2} ξ = 2·ord_0(xiDescent)`: at the FE
fixed point the descent `z ↦ z²` is ramified, so the ξ-order there is exactly twice the descended
order.  The Phase-C central evenness is therefore automatic — it holds for *any* descended order — so a
center deposit of xiDescent-order `n` is a central ξ-zero of order `2n`, Phase-C-consistent. -/
theorem xi_central_order_eq_two_mul :
    analyticOrderAt xi (1 / 2 : ℂ) = 2 * analyticOrderAt xiDescent 0 := by
  set g : ℂ → ℂ := fun s => (s - 1 / 2) ^ (2 : ℕ) with hg
  have hgan : AnalyticAt ℂ g (1 / 2) := by rw [hg]; exact (analyticAt_id.sub analyticAt_const).pow 2
  have hg0 : g (1 / 2 : ℂ) = 0 := by rw [hg]; norm_num
  have hxian : AnalyticAt ℂ xiDescent (g (1 / 2)) := by
    rw [hg0]; exact xiDescent_analyticOnNhd_univ 0 (Set.mem_univ 0)
  have hcomp := hxian.analyticOrderAt_comp hgan
  have hev : xi =ᶠ[nhds (1 / 2 : ℂ)] xiDescent ∘ g := by
    filter_upwards with z; rw [hg]; exact xi_eq_xiDescent z
  have hgord2 : analyticOrderAt (fun s => g s - g (1 / 2)) (1 / 2) = 2 := by
    rw [hg0, show (fun s => g s - 0) = g from by funext s; rw [sub_zero], hg]
    have hfan : AnalyticAt ℂ (fun s : ℂ => s - 1 / 2) (1 / 2) := analyticAt_id.sub analyticAt_const
    have hderiv : HasDerivAt (fun s : ℂ => s - 1 / 2) 1 (1 / 2) := (hasDerivAt_id _).sub_const _
    have hg' : deriv (fun s : ℂ => s - 1 / 2) (1 / 2) ≠ 0 := by rw [hderiv.deriv]; norm_num
    have key := hfan.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg'
    have hid : (fun z : ℂ => (fun s => s - 1 / 2) z - (fun s : ℂ => s - 1 / 2) (1 / 2))
        = (fun s : ℂ => s - 1 / 2) := by funext z; simp
    rw [hid] at key
    rw [show (fun s : ℂ => (s - 1 / 2) ^ (2 : ℕ)) = (fun s : ℂ => s - 1 / 2) ^ (2 : ℕ) from by funext s; rfl,
      analyticOrderAt_pow hfan, key]
    rfl
  rw [analyticOrderAt_congr hev, hcomp, hgord2, hg0, mul_comm]

/-! ### §4 The verdict -/

/-- **Central parity cannot violate the deposit.**  Under any admissible deformation the seam order
changes by an even amount, so the mod-2 seam parity — precisely the central-parity constraint — is
conserved.  The half-charge deposit therefore can never create a central-parity violation: central
parity does not obstruct it. -/
theorem deposit_respects_central_parity {S₀ S₁ : Finset ℂ} (ord : ℂ → ℕ)
    (h0conj : ∀ w ∈ S₀, (starRingEnd ℂ) w ∈ S₀) (h0ord : ∀ w ∈ S₀, ord ((starRingEnd ℂ) w) = ord w)
    (h1conj : ∀ w ∈ S₁, (starRingEnd ℂ) w ∈ S₁) (h1ord : ∀ w ∈ S₁, ord ((starRingEnd ℂ) w) = ord w)
    (hagg : ∑ w ∈ S₀, ord w = ∑ w ∈ S₁, ord w) :
    seamOrder S₀ ord % 2 = seamOrder S₁ ord % 2 :=
  seamOrder_parity_conserved ord h0conj h0ord h1conj h1ord hagg

end RHTower
