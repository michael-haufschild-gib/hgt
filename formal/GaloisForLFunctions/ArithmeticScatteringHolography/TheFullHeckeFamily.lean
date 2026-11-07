import GaloisForLFunctions.ArithmeticScatteringHolography.TheCuspidalSector

/-!
# The full Hecke family of a black hole

A place of even degree `2m` of a curve sees the second group: on the cusp form `θ_ψ` it acts by `(-q)^m (ψ(w) + ψ(-w))`. The operator with these eigenvalues
is explicit on every black hole with odd groups:

  `T_{Q, m, w} = P_{2m}(T_Q) + (-q)^m Λ_w`  (`heckeFull`),

and at `m = 1` it is `heckeTwo` (`heckeFull_zero`). So the family `T_Q`, `P_{2n+1}(T_Q)`, `T_{Q, m, w}` has the shape of the Hecke algebra at places of all degrees:

* it commutes with `A` and with itself (`heckeFull_comm_waveOp`, `heckeFull_comm`), and has `q^{2m} + 1` edges (`heckeFull_one`);
* it acts in the cusps by the shift by `2m` (`heckeFull_ray`), on a resonance by `X^{2m} + Y^{2m}` (`heckeFull_resonance`), and on a cusp form by the arithmetic eigenvalue
  (`heckeFull_thetaField`);
* it is symmetric on compactly supported functions (`heckeFull_symmetric`);
* **for `w ≠ 0` and `q ≥ 7` all its coefficients are nonnegative** (`heckeFull_nonneg`).

So this algebra exists on the fakes, with the positivity one asks of it, and with the resonances off the circle
(`universal_damping_not_forced_by_the_full_algebra`). **Commutation, positivity, the edge count, the shape in the cusps and the eigenvalues, at places of all degrees, do not separate
a curve from a fake.**
-/

open Finset
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G G' : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [AddCommGroup G'] [DecidableEq G']
  [Fintype G']

/-- **Hecke at a place of degree `2(n+1)`**, of class `2(n+1) Q` and of class `w` on the second group. -/
def heckeFull (q : ℕ) (Q : G) (n : ℕ) (w : G') (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) : ℂ :=
  heckeDeg q Q (2 * n + 2) f v + (-(q : ℂ)) ^ (n + 1) * thetaOp q w f v

variable (B : Channels G (DeadLabel G')) (hG : ∀ P : G, 2 • P = 0 → P = 0)
  (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0)

include hG hG' in
/-- At degree two the family is `heckeTwo`. -/
theorem heckeFull_zero (Q : G) (w : G') (f : Vertex G (DeadLabel G') → ℂ) (v : Vertex G (DeadLabel G')) :
    heckeFull B.q Q 0 w f v = heckeTwo B.q B.trace (2 • Q) w f v := by
  rw [heckeTwo_eq B hG hG']
  unfold heckeFull
  simp only [zero_add, pow_one, mul_zero]
  ring

/-- `Λ_w` kills the constants, so the family has `q^{2m} + 1` edges. -/
theorem heckeFull_one (Q : G) (n : ℕ) (w : G') (v : Vertex G (DeadLabel G')) :
    heckeFull B.q Q n w (fun _ => (1 : ℂ)) v = (B.q : ℂ) ^ (2 * n + 2) + 1 := by
  have hq := B.q_ne_zero
  have hc : ∀ Q' : G', thetaTerm B.q (fun _ : Vertex G (DeadLabel G') => (1 : ℂ)) Q' = 1 := by
    intro Q'
    unfold thetaTerm deadTerm deadTermB
    split_ifs
    · field_simp
      ring
    · field_simp
  unfold heckeFull
  rw [heckeDeg_one_const, thetaOp_of_const B.q w hc v]
  ring

theorem heckeFull_ray (q : ℕ) (Q : G) (n : ℕ) (w : G') (f : Vertex G (DeadLabel G') → ℂ) (P : G) (j : ℕ) :
    heckeFull q Q n w f (.ray P (2 * n + 2 + j)) =
      (q : ℂ) ^ (2 * n + 2) * f (.ray (P + (2 * n + 2) • Q) j) +
        f (.ray (P - (2 * n + 2) • Q) (2 * (2 * n + 2) + j)) := by
  unfold heckeFull
  rw [heckeDeg_ray, thetaOp_ray]
  ring

include hG hG' in
theorem heckeFull_comm_waveOp (Q : G) (n : ℕ) (w : G') (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) :
    waveOp B.q (heckeFull B.q Q n w f) v = heckeFull B.q Q n w (waveOp B.q f) v := by
  have e : heckeFull B.q Q n w f = fun u => heckeDeg B.q Q (2 * n + 2) f u -
      (-(-(B.q : ℂ)) ^ (n + 1)) * thetaOp B.q w f u := by
    funext u
    unfold heckeFull
    ring
  rw [e, waveOp_sub_smul, waveOp_thetaOp B hG hG', heckeDeg_comm_waveOp]
  unfold heckeFull
  rw [thetaOp_waveOp]
  ring

include hG hG' in
/-- **The operators of the family commute.** -/
theorem heckeFull_comm (Q R : G) (n m : ℕ) (w u : G') (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) :
    heckeFull B.q Q n w (heckeFull B.q R m u f) v = heckeFull B.q R m u (heckeFull B.q Q n w f) v := by
  have key (Q R : G) (n m : ℕ) (w u : G') : heckeFull B.q Q n w (heckeFull B.q R m u f) v =
      heckeDeg B.q Q (2 * n + 2) (heckeDeg B.q R (2 * m + 2) f) v +
        2 * (-(B.q : ℂ)) ^ (n + 1) * (-(B.q : ℂ)) ^ (m + 1) * thetaOp B.q u f v +
        2 * (-(B.q : ℂ)) ^ (n + 1) * (-(B.q : ℂ)) ^ (m + 1) * thetaOp B.q w f v +
        (-(B.q : ℂ)) ^ (n + 1) * (-(B.q : ℂ)) ^ (m + 1) * thetaOp B.q w (thetaOp B.q u f) v := by
    have e : heckeFull B.q R m u f = fun x => heckeDeg B.q R (2 * m + 2) f x -
        (-(-(B.q : ℂ)) ^ (m + 1)) * thetaOp B.q u f x := by
      funext x
      unfold heckeFull
      ring
    have hP (x : Vertex G (DeadLabel G')) : heckeDeg B.q Q (2 * n + 2) (thetaOp B.q u f) x =
        2 * (-(B.q : ℂ)) ^ (n + 1) * thetaOp B.q u f x := by
      have := (heckeDeg_thetaOp B hG hG' Q u f (n + 1) x).2
      rwa [show 2 * (n + 1) = 2 * n + 2 by ring] at this
    have hL : thetaOp B.q w (heckeDeg B.q R (2 * m + 2) f) v =
        2 * (-(B.q : ℂ)) ^ (m + 1) * thetaOp B.q w f v := by
      have := (thetaOp_heckeDeg B R w f (m + 1) v).2
      rwa [show 2 * (m + 1) = 2 * m + 2 by ring] at this
    show heckeDeg B.q Q (2 * n + 2) (heckeFull B.q R m u f) v +
      (-(B.q : ℂ)) ^ (n + 1) * thetaOp B.q w (heckeFull B.q R m u f) v = _
    rw [e, heckeDeg_sub_smul, thetaOp_sub_smul, hP, hL]
    ring
  rw [key Q R n m w u, key R Q m n u w, heckeDeg_comm B Q R, thetaOp_comm B w u]
  ring

include hG hG' in
/-- **The family acts on a resonance by the dispersion relation**, wherever the resonance is. -/
theorem heckeFull_resonance (Q : G) (n : ℕ) (w : G') {X Y : ℂ} (hXY : X * Y = B.q) (hne : X ≠ Y)
    (hlam : X + Y ≠ 0) {f : Vertex G (DeadLabel G') → ℂ} {c : G → ℂ} (hf : IsOutgoing B.q X Y f c)
    (v : Vertex G (DeadLabel G')) :
    heckeFull B.q Q n w f v = (X ^ (2 * n + 2) + Y ^ (2 * n + 2)) * f v := by
  unfold heckeFull
  rw [heckeDeg_resonance B Q (2 * n + 2) hXY hne hlam hf]
  have hfun : f = fun x => ((X + Y)⁻¹) * waveOp B.q f x := by
    funext x
    rw [hf.eigen x]
    field_simp
  have hzero : thetaOp B.q w f v = 0 := by
    rw [hfun, thetaOp_smul, thetaOp_waveOp]
    ring
  rw [hzero]
  ring

include hG hG' in
/-- **On a cusp form the family has the arithmetic eigenvalue.** -/
theorem heckeFull_thetaField {ψ : AddChar G' ℂ} (hψ : ψ ≠ 1) (Q : G) (n : ℕ) (w : G')
    (v : Vertex G (DeadLabel G')) :
    heckeFull B.q Q n w (thetaField G B.q ψ) v =
      (-(B.q : ℂ)) ^ (n + 1) * (ψ w + ψ (-w)) * thetaField G B.q ψ v := by
  unfold heckeFull
  have h := (heckeDeg_thetaField B hG hG' hψ Q (n + 1) v).2
  rw [show 2 * (n + 1) = 2 * n + 2 by ring] at h
  rw [h, thetaOp_thetaField B hG hG']
  ring

include hG hG' in
/-- **The family is symmetric on compactly supported functions.** -/
theorem heckeFull_symmetric (Q : G) (n : ℕ) (w : G') {f : Vertex G (DeadLabel G') → ℂ}
    (g : Vertex G (DeadLabel G') → ℂ) {K M : ℕ} (hf : CompactAt f K) (hM : K + (2 * n + 2) + 1 ≤ M) :
    truncSum M (fun v => mass B.q v *
      (heckeFull B.q Q n w f v * g v - f v * heckeFull B.q Q n w g v)) = 0 := by
  have key : ∀ v, mass B.q v * (heckeFull B.q Q n w f v * g v - f v * heckeFull B.q Q n w g v) =
      mass B.q v * (heckeDeg B.q Q (2 * n + 2) f v * g v - f v * heckeDeg B.q Q (2 * n + 2) g v) +
        (-(B.q : ℂ)) ^ (n + 1) *
          (mass B.q v * (thetaOp B.q w f v * g v - f v * thetaOp B.q w g v)) := by
    intro v
    unfold heckeFull
    ring
  rw [truncSum_congr M key, truncSum_add, truncSum_smul, heckeDeg_symmetric B Q (2 * n + 2) g hf hM,
    truncSum_thetaOp_green B hG' hG]
  ring

/-! ### Positivity -/

/-- The translation of the cusps does not move the shadow. -/
theorem thetaOp_transl (q : ℕ) (Q : G) (w : G') (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) :
    thetaOp q w (fun u => f (transl (-Q) u)) (transl Q v) = thetaOp q w f v := by
  have ht (Q' : G') : thetaTerm q (fun u => f (transl (-Q) u)) Q' = thetaTerm q f Q' := by
    unfold thetaTerm deadTerm deadTermB
    split_ifs <;> rfl
  rcases v with _ | d | x | L | ⟨P, k⟩
  · rfl
  · show thetaOp q w _ (.dead d) = thetaOp q w f (.dead d)
    rw [thetaOp_dead', thetaOp_dead']
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h R =>
      change thetaDiff q _ w R = thetaDiff q f w R
      unfold thetaDiff
      rw [ht, ht, ht]
  · induction x using Quotient.inductionOn with
    | h P =>
      change thetaNeck q _ w P = thetaNeck q f w P
      unfold thetaNeck
      rw [ht, ht]
  · show thetaOp q w _ (.cap L) = thetaOp q w f (.cap L)
    rw [thetaOp_cap, thetaOp_cap, ht, ht]
  · rfl

section Positivity

variable (hq : 7 ≤ B.q) {f : Vertex G (DeadLabel G') → ℂ} (hf : ∀ v, 0 ≤ f v)

local notation "qr" => (B.q : ℝ)
local notation "tr" => B.traceR

include hG hG' hq hf in
/-- The reading of the two sums with two dead ends. -/
theorem pair_nonneg₂ {α β e : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hB : β ≤ α) (he : 0 ≤ β + e)
    {d₁ d₂ : DeadLabel G'} (hd : d₁ ≠ d₂) :
    0 ≤ (α : ℂ) * sOne B.q f + (β : ℂ) * sTwo B.q f + 2 * (e : ℂ) * f (.dead d₁) +
      2 * (e : ℂ) * f (.dead d₂) := by
  have hq0 := B.q_ne_zero
  have hqr : (7 : ℝ) ≤ qr := qr_ge B hq
  have hqr0 : (0 : ℝ) < qr := by linarith
  have hgap : ∑ P : G, gapOp B.q f P =
      gapOp B.q f 0 + (B.q : ℂ) * ∑ P ∈ univ.erase (0 : G), f (.neck (Branch.mk P)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : G)), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun P hP => ?_
    have hP0 : ¬ 2 • P = 0 := fun h => (Finset.mem_erase.mp hP).1 (hG P h)
    unfold gapOp
    rw [dif_neg hP0]
  have hdead := sum_deadTerm B.q f hG'
  have hsplit : ∑ d : DeadLabel G', f (.dead d) =
      f (.dead d₁) + (f (.dead d₂) + ∑ d ∈ (univ.erase d₁).erase d₂, f (.dead d)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ d₁),
      ← Finset.add_sum_erase (univ.erase d₁) _ (Finset.mem_erase.mpr ⟨hd.symm, Finset.mem_univ d₂⟩)]
  have hN : 0 ≤ ∑ P ∈ univ.erase (0 : G), f (.neck (Branch.mk P)) :=
    Finset.sum_nonneg fun _ _ => hf _
  have hD : 0 ≤ ∑ d ∈ (univ.erase d₁).erase d₂, f (.dead d) := Finset.sum_nonneg fun _ _ => hf _
  have key : (α : ℂ) * sOne B.q f + (β : ℂ) * sTwo B.q f + 2 * (e : ℂ) * f (.dead d₁) +
        2 * (e : ℂ) * f (.dead d₂) =
      (((α * (qr - 1) + β * (qr + 1)) / qr : ℝ) : ℂ) * f (.neck (Branch.mk 0)) +
        (((α - β) / qr : ℝ) : ℂ) * f (.cap (capZero G)) +
        (α : ℂ) * ∑ P ∈ univ.erase (0 : G), f (.neck (Branch.mk P)) +
        ((2 * β : ℝ) : ℂ) * ∑ d ∈ (univ.erase d₁).erase d₂, f (.dead d) +
        ((2 * (β + e) : ℝ) : ℂ) * f (.dead d₁) + ((2 * (β + e) : ℝ) : ℂ) * f (.dead d₂) := by
    unfold sOne sTwo
    rw [hgap, hdead, hsplit, gapOp_zero_eq, deadTerm_zero_eq]
    push_cast
    field_simp
    ring
  rw [key]
  have c1 : 0 ≤ (α * (qr - 1) + β * (qr + 1)) / qr :=
    div_nonneg (add_nonneg (mul_nonneg hα (by linarith)) (mul_nonneg hβ (by linarith))) hqr0.le
  have c2 : 0 ≤ (α - β) / qr := div_nonneg (by linarith) hqr0.le
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (ofReal_nonneg' c1) (hf _)) (mul_nonneg (ofReal_nonneg' c2) (hf _)))
    (mul_nonneg (ofReal_nonneg' hα) hN)) (mul_nonneg (ofReal_nonneg' (by linarith)) hD))
    (mul_nonneg (ofReal_nonneg' (by linarith)) (hf _)))
    (mul_nonneg (ofReal_nonneg' (by linarith)) (hf _))

/-- The sum of the shadow terms at a nonzero class is the dead end. -/
theorem thetaTerm_dead (q : ℕ) (hq0 : (q : ℂ) ≠ 0) (g : Vertex G (DeadLabel G') → ℂ) {Q : G'}
    (h : Branch.mk Q ≠ Branch.mk 0) : thetaTerm q g Q = g (.dead ⟨Branch.mk Q, h⟩) := by
  unfold thetaTerm deadTerm deadTermB
  rw [dif_neg h]
  field_simp

include hG hG' hq hf in
/-- **The core of the positivity of the family**: `P_{2N+2}(A) + (-q)^{N+1} Λ_w` has nonnegative coefficients, for `N ≥ 1` and `w ≠ 0`. -/
theorem chebOp_add_theta_nonneg (n : ℕ) {w : G'} (hw : w ≠ 0) (v : Vertex G (DeadLabel G')) :
    0 ≤ chebOp B.q (2 * (n + 1) + 2) f v + (-(B.q : ℂ)) ^ (n + 2) * thetaOp B.q w f v := by
  have h7 := qr_ge B hq
  have ht := tr_le B
  have hne0 := B.q_ne_zero
  have hq1' : (0 : ℝ) ≤ qr - 1 := by linarith
  have hq2' : (0 : ℝ) ≤ qr + 1 := by linarith
  have hq1 : (0 : ℂ) ≤ (B.q : ℂ) - 1 := by simpa using ofReal_nonneg' hq1'
  have hq2 : (0 : ℂ) ≤ (B.q : ℂ) + 1 := by simpa using ofReal_nonneg' hq2'
  have h12 := half_nonneg_C
  have hbase (u : Vertex G (DeadLabel G')) (hu : thetaOp B.q w f u = 0) :
      0 ≤ chebOp B.q (2 * (n + 1) + 2) f u + (-(B.q : ℂ)) ^ (n + 2) * thetaOp B.q w f u := by
    rw [hu, mul_zero, add_zero]
    exact chebOp_nonneg B hG hG' hq hf (by omega) u
  have hmkw : Branch.mk w ≠ Branch.mk (0 : G') := by
    intro h
    rcases mk_eq_mk_iff.mp h with h | h
    · exact hw h.symm
    · apply hw
      simpa [neg_eq_zero, eq_comm] using h
  have hconvη : 0 ≤ convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) :=
    convC_nonneg (etaS_nonneg h7 ht) (fun k => aS_nonneg hf _) _
  have hconvσ : 0 ≤ convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) :=
    convC_nonneg (sigmaS_nonneg h7 ht) (fun k => aS_nonneg hf _) _
  obtain ⟨hTcl, hWcl, hVcl⟩ := odd_closed B f hG hG' (n + 1)
  have hσ := sigmaS_nonneg h7 ht (n + 1)
  have hη := etaS_nonneg h7 ht (n + 1)
  have hγ' := gpS_nonneg h7 ht (n + 1)
  have hησ := etaS_le_sigmaS h7 ht (n + 1)
  have hγη := gpS_le_etaS h7 ht (n + 1)
  have hpin := gp_pin h7 ht n
  have heta := eta_sub_gp_ge h7 ht n
  have hZ := second_diff_nonneg h7 ht n
  set θ : ℝ := (-qr) ^ (n + 2) with hθ
  have hθC : (-(B.q : ℂ)) ^ (n + 2) = (θ : ℂ) := by
    rw [hθ]
    push_cast
    rfl
  rcases v with _ | d | x | L | ⟨P, k⟩
  · exact hbase _ rfl
  · -- a dead end
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h Q =>
      have hx' : Branch.mk Q ≠ Branch.mk 0 := hx
      change 0 ≤ chebOp B.q (2 * (n + 1) + 2) f (.dead ⟨Branch.mk Q, hx'⟩) +
        (-(B.q : ℂ)) ^ (n + 2) * thetaDiff B.q f w Q
      have hQ0 : Q ≠ 0 := by
        rintro rfl
        exact hx' rfl
      have hdist : Branch.mk (Q + w) ≠ Branch.mk (Q - w) := by
        intro h
        rcases mk_eq_mk_iff.mp h with h | h
        · apply hw
          apply hG'
          rw [two_nsmul]
          have e : (Q + w) - (Q - w) = w + w := by abel
          rw [← e, ← h]
          abel
        · apply hQ0
          apply hG'
          rw [two_nsmul]
          have e : Q + Q = (Q - w) + (Q + w) := by abel
          rw [e, h]
          abel
      rw [dead_row_even B f (n + 1) hx', hVcl]
      unfold thetaDiff
      rw [thetaTerm_dead B.q hne0 f hx', hθC]
      have hα0 : 0 ≤ (qr + 1) * etaS qr tr (n + 1) / 2 := div_nonneg (mul_nonneg hq2' hη) (by norm_num)
      have hβ0 : 0 ≤ (qr + 1) * gpS qr tr (n + 1) / 2 := div_nonneg (mul_nonneg hq2' hγ') (by norm_num)
      have hle : (qr + 1) * gpS qr tr (n + 1) / 2 ≤ (qr + 1) * etaS qr tr (n + 1) / 2 := by
        have := mul_le_mul_of_nonneg_left hγη hq2'
        linarith
      have hbig : 0 ≤ (qr + 1) * gpS qr tr (n + 1) + θ := by
        have : qr * gpS qr tr (n + 1) ≤ (qr + 1) * gpS qr tr (n + 1) := by nlinarith
        linarith
      have hconv : 0 ≤ ((B.q : ℂ) + 1) * convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) :=
        mul_nonneg hq2 hconvη
      by_cases h₁ : Branch.mk (Q + w) = Branch.mk 0
      · -- the first translate is the shadow at zero
        have hQw : Q + w = 0 := by
          rcases mk_eq_mk_iff.mp h₁ with h | h
          · exact h.symm
          · exact neg_eq_zero.mp h.symm
        have h₂ : Branch.mk (Q - w) ≠ Branch.mk 0 := fun h => hdist (h₁.trans h.symm)
        rw [hQw, thetaTerm_dead B.q hne0 f h₂]
        have hp := pair_nonneg B hG hG' hq hf (α := (qr + 1) * etaS qr tr (n + 1) / 2)
          (β := (qr + 1) * gpS qr tr (n + 1) / 2) (β₀ := (qr + 1) * gpS qr tr (n + 1) / 2 + θ)
          (e := θ / 2) hα0 hβ0
          (by
            have : (qr + 1) * etaS qr tr (n + 1) / 2 - (qr + 1) * gpS qr tr (n + 1) / 2 =
                (qr + 1) * (etaS qr tr (n + 1) - gpS qr tr (n + 1)) / 2 := by ring
            linarith)
          (by
            have e : (qr + 1) * etaS qr tr (n + 1) / 2 * (qr - 1) +
                ((qr + 1) * gpS qr tr (n + 1) / 2 + θ) * (qr + 1) =
                (qr + 1) * ((qr - 1) * (etaS qr tr (n + 1) - gpS qr tr (n + 1)) / 2 +
                  (qr * gpS qr tr (n + 1) + θ)) := by ring
            rw [e]
            exact mul_nonneg hq2' (add_nonneg
              (div_nonneg (mul_nonneg hq1' (by linarith)) (by norm_num)) hpin))
          (by linarith) ⟨Branch.mk (Q - w), h₂⟩
        have e1 : ((B.q : ℂ) + 1) * ((1 / 2 : ℂ) * (etaS qr tr (n + 1) : ℂ) * sOne B.q f +
              (1 / 2 : ℂ) * (gpS qr tr (n + 1) : ℂ) * sTwo B.q f +
              convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1)) +
              2 * (θ : ℂ) * f (.dead ⟨Branch.mk Q, hx'⟩) +
              (θ : ℂ) * (thetaTerm B.q f 0 + f (.dead ⟨Branch.mk (Q - w), h₂⟩) -
                2 * f (.dead ⟨Branch.mk Q, hx'⟩)) =
            (((qr + 1) * etaS qr tr (n + 1) / 2 : ℝ) : ℂ) * sOne B.q f +
              (((qr + 1) * gpS qr tr (n + 1) / 2 : ℝ) : ℂ) * sTwo B.q f +
              (((qr + 1) * gpS qr tr (n + 1) / 2 + θ - (qr + 1) * gpS qr tr (n + 1) / 2 : ℝ) : ℂ) *
                (deadTerm B.q f (0 : G') / B.q) +
              2 * ((θ / 2 : ℝ) : ℂ) * f (.dead ⟨Branch.mk (Q - w), h₂⟩) +
              ((B.q : ℂ) + 1) * convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) := by
          unfold thetaTerm
          push_cast
          ring
        rw [e1]
        exact add_nonneg hp hconv
      · by_cases h₂ : Branch.mk (Q - w) = Branch.mk 0
        · have hQw : Q - w = 0 := by
            rcases mk_eq_mk_iff.mp h₂ with h | h
            · exact h.symm
            · exact neg_eq_zero.mp h.symm
          rw [hQw, thetaTerm_dead B.q hne0 f h₁]
          have hp := pair_nonneg B hG hG' hq hf (α := (qr + 1) * etaS qr tr (n + 1) / 2)
            (β := (qr + 1) * gpS qr tr (n + 1) / 2) (β₀ := (qr + 1) * gpS qr tr (n + 1) / 2 + θ)
            (e := θ / 2) hα0 hβ0
            (by
              have : (qr + 1) * etaS qr tr (n + 1) / 2 - (qr + 1) * gpS qr tr (n + 1) / 2 =
                  (qr + 1) * (etaS qr tr (n + 1) - gpS qr tr (n + 1)) / 2 := by ring
              linarith)
            (by
              have e : (qr + 1) * etaS qr tr (n + 1) / 2 * (qr - 1) +
                  ((qr + 1) * gpS qr tr (n + 1) / 2 + θ) * (qr + 1) =
                  (qr + 1) * ((qr - 1) * (etaS qr tr (n + 1) - gpS qr tr (n + 1)) / 2 +
                    (qr * gpS qr tr (n + 1) + θ)) := by ring
              rw [e]
              exact mul_nonneg hq2' (add_nonneg
                (div_nonneg (mul_nonneg hq1' (by linarith)) (by norm_num)) hpin))
            (by linarith) ⟨Branch.mk (Q + w), h₁⟩
          have e1 : ((B.q : ℂ) + 1) * ((1 / 2 : ℂ) * (etaS qr tr (n + 1) : ℂ) * sOne B.q f +
                (1 / 2 : ℂ) * (gpS qr tr (n + 1) : ℂ) * sTwo B.q f +
                convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1)) +
                2 * (θ : ℂ) * f (.dead ⟨Branch.mk Q, hx'⟩) +
                (θ : ℂ) * (f (.dead ⟨Branch.mk (Q + w), h₁⟩) + thetaTerm B.q f 0 -
                  2 * f (.dead ⟨Branch.mk Q, hx'⟩)) =
              (((qr + 1) * etaS qr tr (n + 1) / 2 : ℝ) : ℂ) * sOne B.q f +
                (((qr + 1) * gpS qr tr (n + 1) / 2 : ℝ) : ℂ) * sTwo B.q f +
                (((qr + 1) * gpS qr tr (n + 1) / 2 + θ - (qr + 1) * gpS qr tr (n + 1) / 2 : ℝ) : ℂ) *
                  (deadTerm B.q f (0 : G') / B.q) +
                2 * ((θ / 2 : ℝ) : ℂ) * f (.dead ⟨Branch.mk (Q + w), h₁⟩) +
                ((B.q : ℂ) + 1) * convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) := by
            unfold thetaTerm
            push_cast
            ring
          rw [e1]
          exact add_nonneg hp hconv
        · have hlab : (⟨Branch.mk (Q + w), h₁⟩ : DeadLabel G') ≠ ⟨Branch.mk (Q - w), h₂⟩ := by
            intro h
            exact hdist (congrArg Subtype.val h)
          rw [thetaTerm_dead B.q hne0 f h₁, thetaTerm_dead B.q hne0 f h₂]
          have hp := pair_nonneg₂ B hG hG' hq hf (α := (qr + 1) * etaS qr tr (n + 1) / 2)
            (β := (qr + 1) * gpS qr tr (n + 1) / 2) (e := θ / 2) hα0 hβ0 hle (by linarith) hlab
          have e1 : ((B.q : ℂ) + 1) * ((1 / 2 : ℂ) * (etaS qr tr (n + 1) : ℂ) * sOne B.q f +
                (1 / 2 : ℂ) * (gpS qr tr (n + 1) : ℂ) * sTwo B.q f +
                convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1)) +
                2 * (θ : ℂ) * f (.dead ⟨Branch.mk Q, hx'⟩) +
                (θ : ℂ) * (f (.dead ⟨Branch.mk (Q + w), h₁⟩) + f (.dead ⟨Branch.mk (Q - w), h₂⟩) -
                  2 * f (.dead ⟨Branch.mk Q, hx'⟩)) =
              (((qr + 1) * etaS qr tr (n + 1) / 2 : ℝ) : ℂ) * sOne B.q f +
                (((qr + 1) * gpS qr tr (n + 1) / 2 : ℝ) : ℂ) * sTwo B.q f +
                2 * ((θ / 2 : ℝ) : ℂ) * f (.dead ⟨Branch.mk (Q + w), h₁⟩) +
                2 * ((θ / 2 : ℝ) : ℂ) * f (.dead ⟨Branch.mk (Q - w), h₂⟩) +
                ((B.q : ℂ) + 1) * convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) := by
            push_cast
            ring
          rw [e1]
          exact add_nonneg hp hconv
  · -- a neck
    induction x using Quotient.inductionOn with
    | h P =>
      change 0 ≤ chebOp B.q (2 * (n + 1) + 2) f (.neck (Branch.mk P)) +
        (-(B.q : ℂ)) ^ (n + 2) * thetaOp B.q w f (.neck (Branch.mk P))
      by_cases hP : P = 0
      · subst hP
        rw [thetaOp_neck, pin_of_terms B.q hne0 (chebOp B.q (2 * (n + 1) + 2) f),
          show 2 * (n + 1) + 2 = (2 * (n + 1) + 1) + 1 by ring, gap_formula,
          show (2 * (n + 1) + 1) + 1 = 2 * (n + 1) + 2 by ring, deadTerm_even, hWcl, hVcl]
        unfold thetaNeck
        rw [if_pos (by simp : 2 • (0 : G) = 0), thetaTerm_dead B.q hne0 f hmkw, hθC, neg_zero]
        set α : ℝ := (qr - 1) * sigmaS qr tr (n + 1) / 4 + (qr + 1) * etaS qr tr (n + 1) / 4 with hα
        set β : ℝ := (qr - 1) * etaS qr tr (n + 1) / 4 + (qr + 1) * gpS qr tr (n + 1) / 4 with hβ
        have hα0 : 0 ≤ α := add_nonneg (div_nonneg (mul_nonneg hq1' hσ) (by norm_num))
          (div_nonneg (mul_nonneg hq2' hη) (by norm_num))
        have hβ0 : 0 ≤ β := add_nonneg (div_nonneg (mul_nonneg hq1' hη) (by norm_num))
          (div_nonneg (mul_nonneg hq2' hγ') (by norm_num))
        have hle : β ≤ α := by
          rw [hα, hβ]
          have a1 := mul_le_mul_of_nonneg_left hησ hq1'
          have a2 := mul_le_mul_of_nonneg_left hγη hq2'
          linarith
        have hp := pair_nonneg B hG hG' hq hf (α := α) (β := β) (β₀ := β) (e := θ / 2) hα0 hβ0 hle
          (add_nonneg (mul_nonneg hα0 hq1') (mul_nonneg hβ0 hq2'))
          (by
            rw [hβ]
            have a1 := mul_le_mul_of_nonneg_left hγη hq1'
            have e : (qr - 1) * gpS qr tr (n + 1) / 4 + (qr + 1) * gpS qr tr (n + 1) / 4 + θ / 2 =
                (qr * gpS qr tr (n + 1) + θ) / 2 := by ring
            linarith)
          ⟨Branch.mk w, hmkw⟩
        have e1 : ((B.q : ℂ) * (f (.ray 0 (2 * (n + 1) + 1)) + f (.ray 0 (2 * (n + 1) + 1)) +
            ((B.q : ℂ) - 1) * ((1 / 2 : ℂ) * (sigmaS qr tr (n + 1) : ℂ) * sOne B.q f +
              (1 / 2 : ℂ) * (etaS qr tr (n + 1) : ℂ) * sTwo B.q f +
              convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1))) +
            ((B.q : ℂ) * (((B.q : ℂ) + 1) * ((1 / 2 : ℂ) * (etaS qr tr (n + 1) : ℂ) * sOne B.q f +
              (1 / 2 : ℂ) * (gpS qr tr (n + 1) : ℂ) * sTwo B.q f +
              convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1))) +
            2 * (θ : ℂ) * deadTerm B.q f (0 : G'))) / (2 * (B.q : ℂ)) +
            (θ : ℂ) * (f (.dead ⟨Branch.mk w, hmkw⟩) - thetaTerm B.q f 0) =
            ((α : ℂ) * sOne B.q f + (β : ℂ) * sTwo B.q f +
              ((β - β : ℝ) : ℂ) * (deadTerm B.q f (0 : G') / B.q) +
              2 * ((θ / 2 : ℝ) : ℂ) * f (.dead ⟨Branch.mk w, hmkw⟩)) +
            f (.ray 0 (2 * (n + 1) + 1)) +
            (1 / 2 : ℂ) * (((B.q : ℂ) - 1) * convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1)) +
            (1 / 2 : ℂ) * (((B.q : ℂ) + 1) * convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1)) := by
          unfold thetaTerm
          rw [hα, hβ]
          push_cast
          field_simp
          ring
        rw [e1]
        exact add_nonneg (add_nonneg (add_nonneg hp (hf _))
          (mul_nonneg h12 (mul_nonneg hq1 hconvσ))) (mul_nonneg h12 (mul_nonneg hq2 hconvη))
      · have hP' : ¬ 2 • P = 0 := fun h => hP (hG P h)
        refine hbase _ ?_
        rw [thetaOp_neck]
        unfold thetaNeck
        rw [if_neg hP']
  · -- the cap
    have hL : L = capZero G := Subtype.ext (hG L.1 L.2)
    subst hL
    rw [thetaOp_cap, cap_of_terms B.q (chebOp B.q (2 * (n + 1) + 2) f),
      pin_of_terms B.q hne0 (chebOp B.q (2 * (n + 1) + 2) f),
      show 2 * (n + 1) + 2 = (2 * (n + 1) + 1) + 1 by ring, gap_formula,
      show (2 * (n + 1) + 1) + 1 = 2 * (n + 1) + 2 by ring, deadTerm_even, hWcl, hVcl,
      thetaTerm_dead B.q hne0 f hmkw, hθC, neg_zero]
    have hsq : 0 ≤ qr ^ 2 - 1 := by nlinarith
    have hsqC : (0 : ℂ) ≤ (B.q : ℂ) ^ 2 - 1 := by simpa using ofReal_nonneg' hsq
    set α : ℝ := (qr ^ 2 - 1) * (sigmaS qr tr (n + 1) - etaS qr tr (n + 1)) / 4 with hα
    set β : ℝ := (qr ^ 2 - 1) * (etaS qr tr (n + 1) - gpS qr tr (n + 1)) / 4 with hβ
    have hα0 : 0 ≤ α := div_nonneg (mul_nonneg hsq (by linarith)) (by norm_num)
    have hβ0 : 0 ≤ β := div_nonneg (mul_nonneg hsq (by linarith)) (by norm_num)
    have hle : β ≤ α := by
      rw [hα, hβ]
      have a1 := mul_nonneg hsq hZ
      have e : (qr ^ 2 - 1) * (sigmaS qr tr (n + 1) - etaS qr tr (n + 1)) / 4 -
          (qr ^ 2 - 1) * (etaS qr tr (n + 1) - gpS qr tr (n + 1)) / 4 =
          (qr ^ 2 - 1) * (sigmaS qr tr (n + 1) - 2 * etaS qr tr (n + 1) + gpS qr tr (n + 1)) / 4 := by
        ring
      linarith
    have hp := pair_nonneg B hG hG' hq hf (α := α) (β := β) (β₀ := β) (e := -((qr - 1) * θ) / 2) hα0 hβ0
      hle (add_nonneg (mul_nonneg hα0 hq1') (mul_nonneg hβ0 hq2'))
      (by
        rw [hβ]
        have e : (qr ^ 2 - 1) * (etaS qr tr (n + 1) - gpS qr tr (n + 1)) / 4 + -((qr - 1) * θ) / 2 =
            (qr - 1) / 2 * ((qr + 1) * (etaS qr tr (n + 1) - gpS qr tr (n + 1)) / 2 - θ) := by
          ring
        rw [e]
        exact mul_nonneg (by linarith) (by linarith))
      ⟨Branch.mk w, hmkw⟩
    have hdiff : 0 ≤ convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) -
        convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) := by
      have hc := convC_linear (x := fun j => sigmaS qr tr j - etaS qr tr j) (y := sigmaS qr tr)
        (z := etaS qr tr) (w := fun _ => 0) (A := 1) (B' := -1) (C := 0) (fun j => by ring)
        (fun k => aS f (2 * k + 1)) (n + 1)
      have h0 := convC_nonneg (x := fun j => sigmaS qr tr j - etaS qr tr j)
        (fun j => by linarith [etaS_le_sigmaS h7 ht j]) (a := fun k => aS f (2 * k + 1))
        (fun k => aS_nonneg hf _) (n + 1)
      rw [hc] at h0
      have e3 : ((1 : ℝ) : ℂ) * convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) +
          ((-1 : ℝ) : ℂ) * convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) +
          ((0 : ℝ) : ℂ) * convC (fun _ => 0) (fun k => aS f (2 * k + 1)) (n + 1) =
          convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) -
            convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) := by
        push_cast
        ring
      rwa [e3] at h0
    have e1 : ((B.q : ℂ) + 1) * (((B.q : ℂ) * (f (.ray 0 (2 * (n + 1) + 1)) +
        f (.ray 0 (2 * (n + 1) + 1)) +
        ((B.q : ℂ) - 1) * ((1 / 2 : ℂ) * (sigmaS qr tr (n + 1) : ℂ) * sOne B.q f +
          (1 / 2 : ℂ) * (etaS qr tr (n + 1) : ℂ) * sTwo B.q f +
          convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1))) +
        ((B.q : ℂ) * (((B.q : ℂ) + 1) * ((1 / 2 : ℂ) * (etaS qr tr (n + 1) : ℂ) * sOne B.q f +
          (1 / 2 : ℂ) * (gpS qr tr (n + 1) : ℂ) * sTwo B.q f +
          convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1))) +
        2 * (θ : ℂ) * deadTerm B.q f (0 : G'))) / (2 * (B.q : ℂ))) -
        ((B.q : ℂ) * (((B.q : ℂ) + 1) * ((1 / 2 : ℂ) * (etaS qr tr (n + 1) : ℂ) * sOne B.q f +
          (1 / 2 : ℂ) * (gpS qr tr (n + 1) : ℂ) * sTwo B.q f +
          convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1))) +
        2 * (θ : ℂ) * deadTerm B.q f (0 : G')) +
        (θ : ℂ) * (-((B.q : ℂ) - 1) * (f (.dead ⟨Branch.mk w, hmkw⟩) - thetaTerm B.q f 0)) =
        ((α : ℂ) * sOne B.q f + (β : ℂ) * sTwo B.q f +
          ((β - β : ℝ) : ℂ) * (deadTerm B.q f (0 : G') / B.q) +
          2 * ((-((qr - 1) * θ) / 2 : ℝ) : ℂ) * f (.dead ⟨Branch.mk w, hmkw⟩)) +
        ((B.q : ℂ) + 1) * f (.ray 0 (2 * (n + 1) + 1)) +
        (1 / 2 : ℂ) * (((B.q : ℂ) ^ 2 - 1) *
          (convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) -
            convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (n + 1))) := by
      unfold thetaTerm
      rw [hα, hβ]
      push_cast
      field_simp
      ring
    rw [e1]
    exact add_nonneg (add_nonneg hp (mul_nonneg hq2 (hf _))) (mul_nonneg h12 (mul_nonneg hsqC hdiff))
  · exact hbase _ rfl

include hG hG' hq hf in
/-- **The full Hecke family is positive**: for `w ≠ 0` and `q ≥ 7`, at every even degree. -/
theorem heckeFull_nonneg (Q : G) (n : ℕ) {w : G'} (hw : w ≠ 0) (v : Vertex G (DeadLabel G')) :
    0 ≤ heckeFull B.q Q n w f v := by
  cases n with
  | zero =>
    rw [heckeFull_zero B hG hG']
    exact B.heckeTwo_nonneg hG' (2 • Q) hw hf v
  | succ m =>
    have h := chebOp_add_theta_nonneg B hG hG' hq (f := fun u => f (transl (-Q) u)) (fun _ => hf _) m hw
      (transl Q v)
    rw [thetaOp_transl] at h
    exact h

end Positivity

/-- **The full Hecke algebra does not exclude the fakes.** For `q ≥ 8`, the black hole with `N = 3`, `N' = 2q - 1` carries operators at all even degrees, with both
classes, that commute with the wave operator and with each other, have nonnegative coefficients for `w ≠ 0`, have the right number of edges, the arithmetic eigenvalues on its
cusp forms, and the right dispersion on its resonances; and it has a resonance slower than universal. -/
theorem universal_damping_not_forced_by_the_full_algebra {q : ℕ} (hq : 8 ≤ q) :
    let B := oddPairChannels q 3 (2 * (q - 1) + 1) (by decide) ⟨q - 1, rfl⟩ (by omega) (by omega)
    (∀ (Q : ZMod 3) (n : ℕ) (w : ZMod (2 * (q - 1) + 1)) (f) (v),
        waveOp B.q (heckeFull B.q Q n w f) v = heckeFull B.q Q n w (waveOp B.q f) v) ∧
      (∀ (Q R : ZMod 3) (n m : ℕ) (w u : ZMod (2 * (q - 1) + 1)) (f) (v),
        heckeFull B.q Q n w (heckeFull B.q R m u f) v =
          heckeFull B.q R m u (heckeFull B.q Q n w f) v) ∧
      (∀ (Q : ZMod 3) (n : ℕ) (w : ZMod (2 * (q - 1) + 1)), w ≠ 0 → ∀ f, (∀ v, 0 ≤ f v) → ∀ v,
        0 ≤ heckeFull B.q Q n w f v) ∧
      (∀ (Q : ZMod 3) (n : ℕ) (w : ZMod (2 * (q - 1) + 1)) (v),
        heckeFull B.q Q n w (fun _ => (1 : ℂ)) v = (B.q : ℂ) ^ (2 * n + 2) + 1) ∧
      (∀ (ψ : AddChar (ZMod (2 * (q - 1) + 1)) ℂ), ψ ≠ 1 → ∀ (Q : ZMod 3) (n : ℕ)
        (w : ZMod (2 * (q - 1) + 1)) (v),
        heckeFull B.q Q n w (thetaField (ZMod 3) B.q ψ) v =
          (-(B.q : ℂ)) ^ (n + 1) * (ψ w + ψ (-w)) * thetaField (ZMod 3) B.q ψ v) ∧
      ∃ (X Y : ℂ) (f : Vertex (ZMod 3) (DeadLabel (ZMod (2 * (q - 1) + 1))) → ℂ) (c : ZMod 3 → ℂ),
        f ≠ 0 ∧ IsOutgoing B.q X Y f c ∧ (B.q : ℝ) < Complex.normSq (X ^ 2) := by
  intro B
  have hG : ∀ P : ZMod 3, 2 • P = 0 → P = 0 := two_nsmul_eq_zero_zmod (by decide)
  have hG' : ∀ Q : ZMod (2 * (q - 1) + 1), 2 • Q = 0 → Q = 0 :=
    two_nsmul_eq_zero_zmod ⟨q - 1, rfl⟩
  have h7 : 7 ≤ B.q := by
    show 7 ≤ q
    omega
  refine ⟨fun Q n w f v => heckeFull_comm_waveOp B hG hG' Q n w f v,
    fun Q R n m w u f v => heckeFull_comm B hG hG' Q R n m w u f v,
    fun Q n w hw f hf v => heckeFull_nonneg B hG hG' h7 hf Q n hw v,
    fun Q n w v => heckeFull_one B Q n w v,
    fun ψ hψ Q n w v => heckeFull_thetaField B hG hG' hψ Q n w v, ?_⟩
  have htr : B.traceR = (q : ℝ) - 2 := by
    show (q : ℝ) + 1 - Fintype.card (ZMod 3) = _
    rw [ZMod.card]
    push_cast
    ring
  have hq' : (8 : ℝ) ≤ q := by exact_mod_cast hq
  have hBq : (B.q : ℝ) = q := rfl
  obtain ⟨X, Y, f, c, hf0, hf, hbig, _⟩ := exists_slow_resonance B (by rw [htr, hBq]; nlinarith)
  exact ⟨X, Y, f, c, hf0, hf, hbig⟩

end GaloisForLFunctions.ArithmeticScatteringHolography

end
