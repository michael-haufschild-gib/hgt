import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

open Filter Topology
open Complex ContinuousLinearMap
open scoped InnerProductSpace

/-!
# Passive multimode Floquet flux obstruction

A positive material-loss form and adjoint neighboring-grade couplings force
any real-quasifrequency Floquet solution with polynomial spatial-Hilbert loss
mass to have zero overlap with the lossy region. Spatial mode mixing is
unrestricted. This theorem does not infer the Hilbert-mass bound from a
weaker spacetime-distribution or from a boundary conormal trace.
-/

namespace RHTower

set_option autoImplicit false


private theorem exponential_forces_zero
    (r A s0 : ℝ) (d : ℕ) (hr : 1 < r) (hs : 0 ≤ s0)
    (h : ∀ k : ℕ, s0 * r ^ k ≤ A * (1 + 2 * (k : ℝ)) ^ d) :
    s0 = 0 := by
  have hc : 0 < Real.log r := Real.log_pos hr
  let p : Polynomial ℝ := Polynomial.C A *
    (1 + Polynomial.C (2 / Real.log r) * Polynomial.X) ^ d
  have hcomp := (Polynomial.tendsto_div_exp_atTop p).comp
    (Filter.Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun k : ℕ =>
      A * (1 + 2 * (k : ℝ)) ^ d / r ^ k) atTop (𝓝 0) := by
    convert hcomp using 1
    funext k
    have hden : r ^ k = Real.exp (Real.log r * (k : ℝ)) := by
      calc
        r ^ k = (Real.exp (Real.log r)) ^ k := by rw [Real.exp_log (lt_trans zero_lt_one hr)]
        _ = Real.exp ((k : ℝ) * Real.log r) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (Real.log r * (k : ℝ)) := by rw [mul_comm]
    simp [p, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X, hden]
    field_simp [ne_of_gt hc]; simp
  have hle : ∀ k : ℕ, s0 ≤ A * (1 + 2 * (k : ℝ)) ^ d / r ^ k := by
    intro k
    exact (le_div_iff₀ (pow_pos (lt_trans zero_lt_one hr) _)).mpr (h k)
  have hs0 : s0 ≤ 0 := ge_of_tendsto hlim (Filter.Eventually.of_forall hle)
  exact le_antisymm hs0 hs

private theorem two_step_growth_forces_zero
    (S : ℕ → ℝ) (r A : ℝ) (d : ℕ) (hr : 1 < r)
    (hS : 0 ≤ S 0)
    (hstep : ∀ n : ℕ, r * S n ≤ S (n + 2))
    (hpoly : ∀ n : ℕ, S n ≤ A * (1 + (n : ℝ)) ^ d) :
    S 0 = 0 := by
  have hpow (k : ℕ) : S 0 * r ^ k ≤ S (2 * k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        S 0 * r ^ (k + 1) = r * (S 0 * r ^ k) := by ring
        _ ≤ r * S (2 * k) := mul_le_mul_of_nonneg_left ih (le_of_lt (lt_trans zero_lt_one hr))
        _ ≤ S (2 * k + 2) := hstep (2 * k)
        _ = S (2 * (k + 1)) := by congr 1
  apply exponential_forces_zero r A (S 0) d hr hS
  intro k
  calc
    S 0 * r ^ k ≤ S (2 * k) := hpow k
    _ ≤ A * (1 + ((2 * k : ℕ) : ℝ)) ^ d := hpoly (2 * k)
    _ = A * (1 + 2 * (k : ℝ)) ^ d := by push_cast; ring

private theorem loss_flux_growth_step
    (S : ℕ → ℝ) (C gamma : ℝ)
    (hC : 0 < C) (hgamma : 0 < gamma)
    (hmono : Monotone S)
    (hflux : ∀ n : ℕ, gamma * S (n + 1) ≤
      C * (S (n + 2) - S n)) (n : ℕ) :
    (1 + gamma / C) * S n ≤ S (n + 2) := by
  have hm := hmono (Nat.le_succ n)
  have hf := hflux n
  have hp : gamma * S n ≤ gamma * S (n + 1) :=
    mul_le_mul_of_nonneg_left hm (le_of_lt hgamma)
  have hd : (gamma / C) * S n ≤ S (n + 2) - S n := by
    calc
      (gamma / C) * S n = (gamma * S n) / C := by ring
      _ ≤ S (n + 2) - S n := (div_le_iff₀ hC).mpr (by
        calc
          gamma * S n ≤ gamma * S (n + 1) := hp
          _ ≤ C * (S (n + 2) - S n) := hf
          _ = (S (n + 2) - S n) * C := by ring)
  nlinarith

/-- A positive-loss flux cannot remain bounded in the sideband direction:
without a polynomial-growth assumption, its cumulative mass obeys an exact
exponential lower bound at every even cutoff. -/
theorem ptr_flux_exponential_growth
    (S : ℕ → ℝ) (C gamma : ℝ)
    (hC : 0 < C) (hgamma : 0 < gamma)
    (hmono : Monotone S)
    (hflux : ∀ n : ℕ, gamma * S (n + 1) ≤
      C * (S (n + 2) - S n)) (k : ℕ) :
    S 0 * (1 + gamma / C) ^ k ≤ S (2 * k) := by
  have hr : 0 ≤ 1 + gamma / C := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      S 0 * (1 + gamma / C) ^ (k + 1) =
          (1 + gamma / C) * (S 0 * (1 + gamma / C) ^ k) := by ring
      _ ≤ (1 + gamma / C) * S (2 * k) :=
          mul_le_mul_of_nonneg_left ih hr
      _ ≤ S (2 * k + 2) := loss_flux_growth_step S C gamma hC hgamma hmono hflux (2 * k)
      _ = S (2 * (k + 1)) := by congr 1

private theorem loss_flux_mass_zero
    (S : ℕ → ℝ) (C gamma A : ℝ) (d : ℕ)
    (hC : 0 < C) (hgamma : 0 < gamma) (hS0 : 0 ≤ S 0)
    (hmono : Monotone S)
    (hflux : ∀ n : ℕ, gamma * S (n + 1) ≤
      C * (S (n + 2) - S n))
    (hpoly : ∀ n : ℕ, S n ≤ A * (1 + (n : ℝ)) ^ d) :
    S 0 = 0 := by
  let r : ℝ := 1 + gamma / C
  have hr : 1 < r := by dsimp [r]; exact lt_add_of_pos_right _ (div_pos hgamma hC)
  have hstep (n : ℕ) : r * S n ≤ S (n + 2) :=
    loss_flux_growth_step S C gamma hC hgamma hmono hflux n
  exact two_step_growth_forces_zero S r A d hr hS0 hstep hpoly

noncomputable def ptrSymMass (g : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g n

private theorem ptrSymMass_zero (g : ℤ → ℝ) : ptrSymMass g 0 = g 0 := by
  simp [ptrSymMass]

private theorem ptrSymMass_succ (g : ℤ → ℝ) (N : ℕ) :
    ptrSymMass g (N + 1) = ptrSymMass g N + g (-(N : ℤ) - 1) + g ((N : ℤ) + 1) := by
  have hdis : Disjoint (Finset.Icc (-(N : ℤ)) (N : ℤ))
      {(-((N : ℤ) + 1)), ((N : ℤ) + 1)} := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h <;> simp only [Finset.mem_Icc] at hx <;> omega
  have hneq : (-((N : ℤ) + 1)) ≠ ((N : ℤ) + 1) := by omega
  unfold ptrSymMass
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Finset.Icc_succ_succ N N, Finset.sum_union hdis]
  have hneg : (-((N : ℤ) + 1)) = -(N : ℤ) - 1 := by ring
  rw [hneg]
  have hne : (-(N : ℤ) - 1) ≠ ((N : ℤ) + 1) := by omega
  simp [hne, add_assoc]

private theorem ptrSymMass_fluxDiff (J : ℤ → ℝ) (N : ℕ) :
    ptrSymMass (fun n => J (n + 1) - J n) N =
      J ((N : ℤ) + 1) - J (-(N : ℤ)) := by
  induction N with
  | zero => simp [ptrSymMass_zero]
  | succ N ih =>
    rw [ptrSymMass_succ, ih]
    simp only [Int.natCast_add, Int.natCast_one]
    have h1 : (-(N : ℤ) - 1) + 1 = -(N : ℤ) := by ring
    have h2 : ((N : ℤ) + 1) + 1 = (N : ℤ) + 2 := by ring
    rw [h1, h2]
    ring

private theorem loss_flux_center_zero
    (g J : ℤ → ℝ) (C gamma A : ℝ) (d : ℕ)
    (hC : 0 < C) (hgamma : 0 < gamma)
    (hg : ∀ n, 0 ≤ g n)
    (hbalance : ∀ n, gamma * g n = J (n + 1) - J n)
    (hJ : ∀ n, |J n| ≤ C * (g (n - 1) + g n))
    (hpoly : ∀ N, ptrSymMass g N ≤ A * (1 + (N : ℝ)) ^ d) :
    g 0 = 0 := by
  let S := ptrSymMass g
  have hS0 : 0 ≤ S 0 := by simpa [S, ptrSymMass_zero] using hg 0
  have hmono : Monotone S := by
    apply monotone_nat_of_le_succ
    intro N
    rw [show S (N + 1) = S N + g (-(N : ℤ) - 1) + g ((N : ℤ) + 1) from ptrSymMass_succ g N]
    have h1 := hg (-(N : ℤ) - 1)
    have h2 := hg ((N : ℤ) + 1)
    linarith
  have hbal (N : ℕ) : gamma * S N = J ((N : ℤ) + 1) - J (-(N : ℤ)) := by
    calc
      gamma * S N = ptrSymMass (fun n => gamma * g n) N := by simp [S, ptrSymMass, Finset.mul_sum]
      _ = ptrSymMass (fun n => J (n + 1) - J n) N := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hbalance n
      _ = _ := ptrSymMass_fluxDiff J N
  have hflux (N : ℕ) : gamma * S (N + 1) ≤ C * (S (N + 2) - S N) := by
    have hb := hbal (N + 1)
    have hjp := hJ ((N : ℤ) + 2)
    have hjm := hJ (-(N : ℤ) - 1)
    have hp : J ((N : ℤ) + 2) ≤ |J ((N : ℤ) + 2)| := le_abs_self _
    have hm : -J (-(N : ℤ) - 1) ≤ |J (-(N : ℤ) - 1)| := neg_le_abs _
    have hs1 := ptrSymMass_succ g N
    have hs2 := ptrSymMass_succ g (N + 1)
    have hneg1 : (-(((N + 1 : ℕ) : ℤ))) = -(N : ℤ) - 1 := by push_cast; ring
    have hneg2 : (-(((N + 1 : ℕ) : ℤ)) - 1) = -(N : ℤ) - 2 := by push_cast; ring
    have hpos1 : (((N + 1 : ℕ) : ℤ) + 1) = (N : ℤ) + 2 := by push_cast; ring
    have hpos2 : ((N : ℤ) + 2 - 1) = (N : ℤ) + 1 := by ring
    have hb' : gamma * ptrSymMass g (N + 1) =
        J ((N : ℤ) + 2) - J (-(N : ℤ) - 1) := by
      simpa only [S, hneg1, hpos1] using hb
    have hjp' : |J ((N : ℤ) + 2)| ≤
        C * (g ((N : ℤ) + 1) + g ((N : ℤ) + 2)) := by
      simpa only [hpos2] using hjp
    have hjm' : |J (-(N : ℤ) - 1)| ≤
        C * (g (-(N : ℤ) - 2) + g (-(N : ℤ) - 1)) := by
      simpa [sub_eq_add_neg, add_assoc] using hjm
    have hs2' : ptrSymMass g (N + 2) = ptrSymMass g (N + 1) +
        g (-(N : ℤ) - 2) + g ((N : ℤ) + 2) := by
      simpa only [Nat.add_assoc, hneg2, hpos1] using hs2
    dsimp [S]
    nlinarith [hs1, hs2', hb', hjp', hjm', hp, hm]
  have hz := loss_flux_mass_zero S C gamma A d hC hgamma hS0 hmono hflux hpoly
  simpa [S, ptrSymMass_zero] using hz

private theorem loss_flux_every_grade_zero
    (g J : ℤ → ℝ) (C gamma : ℝ)
    (hC : 0 < C) (hgamma : 0 < gamma)
    (hg : ∀ n, 0 ≤ g n)
    (hbalance : ∀ n, gamma * g n = J (n + 1) - J n)
    (hJ : ∀ n, |J n| ≤ C * (g (n - 1) + g n))
    (hpoly : ∀ j : ℤ, ∃ A : ℝ, ∃ d : ℕ,
      ∀ N : ℕ, ptrSymMass (fun n => g (n + j)) N ≤ A * (1 + (N : ℝ)) ^ d) :
    ∀ j, g j = 0 := by
  intro j
  obtain ⟨A, d, hp⟩ := hpoly j
  have hshift (n : ℤ) : (n + 1) + j = (n + j) + 1 := by ring
  have hshiftm (n : ℤ) : (n - 1) + j = (n + j) - 1 := by ring
  have hz := loss_flux_center_zero
    (fun n => g (n + j)) (fun n => J (n + j)) C gamma A d
    hC hgamma (fun n => hg (n + j))
    (fun n => by simpa only [hshift] using hbalance (n + j))
    (fun n => by simpa only [hshiftm] using hJ (n + j)) hp
  simpa using hz

private theorem imag_modal_algebra
    (a b d e h : ℂ) (nu gamma : ℝ)
    (ha : a.im = 0) (hh : h.im = 0)
    (hnu : nu ≠ 0)
    (hrec : ((nu ^ 2 : ℝ) : ℂ) * (a + b + d + (I * (gamma : ℂ)) * e) = h) :
    gamma * e.re = -(b.im + d.im) := by
  have hi := congrArg Complex.im hrec
  simp only [Complex.im_ofReal_mul, Complex.add_im] at hi
  have hprod : (I * (gamma : ℂ)) * e = (gamma : ℂ) * (I * e) := by ring
  rw [hprod, Complex.im_ofReal_mul, Complex.I_mul_im] at hi
  rw [ha, hh] at hi
  have hnu2 : nu ^ 2 ≠ 0 := pow_ne_zero _ hnu
  have : b.im + d.im + gamma * e.re = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hnu2
    simpa using hi
  linarith

theorem ptr_passive_multimode_grade_spatial_loss_overlap_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : ℤ → E →ₗ[ℂ] E) (M0 Mp Mm G : E →ₗ[ℂ] E)
    (c : ℤ → E) (nu : ℤ → ℝ) (gamma C : ℝ)
    (hgamma : 0 < gamma) (hC : 0 < C)
    (hnu : ∀ n, nu n ≠ 0)
    (hH : ∀ n x, (inner ℂ x (H n x)).im = 0)
    (hM0 : ∀ x, (inner ℂ x (M0 x)).im = 0)
    (hG : ∀ x, 0 ≤ (inner ℂ x (G x)).re)
    (hAdj : ∀ x y, inner ℂ x (Mm y) =
      starRingEnd ℂ (inner ℂ y (Mp x)))
    (hBound : ∀ x y, |(inner ℂ x (Mp y)).im| ≤
      C * ((inner ℂ x (G x)).re + (inner ℂ y (G y)).re))
    (hrec : ∀ n : ℤ,
      (((nu n)^2 : ℝ) : ℂ) •
        (M0 (c n) + Mp (c (n-1)) + Mm (c (n+1)) +
          (I * (gamma : ℂ)) • G (c n)) = H n (c n))
    (hpoly : ∀ j : ℤ, ∃ A : ℝ, ∃ d : ℕ, ∀ N : ℕ,
      ptrSymMass (fun n => (inner ℂ (c (n+j)) (G (c (n+j)))).re) N
        ≤ A * (1 + (N : ℝ)) ^ d) :
    ∀ n, (inner ℂ (c n) (G (c n))).re = 0 := by
  let g : ℤ → ℝ := fun n => (inner ℂ (c n) (G (c n))).re
  let J : ℤ → ℝ := fun n => (inner ℂ (c n) (Mp (c (n-1)))).im
  have hbalance (n : ℤ) : gamma * g n = J (n+1) - J n := by
    have hinner := congrArg (fun v : E => inner ℂ (c n) v) (hrec n)
    simp only [inner_smul_right, inner_add_right] at hinner
    have hi := imag_modal_algebra
      (inner ℂ (c n) (M0 (c n)))
      (inner ℂ (c n) (Mp (c (n-1))))
      (inner ℂ (c n) (Mm (c (n+1))))
      (inner ℂ (c n) (G (c n)))
      (inner ℂ (c n) (H n (c n))) (nu n) gamma
      (hM0 (c n)) (hH n (c n)) (hnu n) hinner
    have hm : (inner ℂ (c n) (Mm (c (n+1)))).im =
        -(inner ℂ (c (n+1)) (Mp (c n))).im := by
      rw [hAdj, Complex.conj_im]
    dsimp [g, J]
    rw [hm] at hi
    have hn : (n+1)-1 = n := by omega
    rw [hn]
    linarith
  have hJ (n : ℤ) : |J n| ≤ C * (g (n-1) + g n) := by
    simpa only [g, J, add_comm] using hBound (c n) (c (n-1))
  have hz := loss_flux_every_grade_zero g J C gamma hC hgamma
    (fun n => hG (c n)) hbalance hJ hpoly
  exact hz

/-- Fixed spatial operators are a specialization of the grade-dependent
loss-flux obstruction. -/
theorem ptr_passive_multimode_tempered_loss_overlap_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H M0 Mp Mm G : E →ₗ[ℂ] E)
    (c : ℤ → E) (nu : ℤ → ℝ) (gamma C : ℝ)
    (hgamma : 0 < gamma) (hC : 0 < C)
    (hnu : ∀ n, nu n ≠ 0)
    (hH : ∀ x, (inner ℂ x (H x)).im = 0)
    (hM0 : ∀ x, (inner ℂ x (M0 x)).im = 0)
    (hG : ∀ x, 0 ≤ (inner ℂ x (G x)).re)
    (hAdj : ∀ x y, inner ℂ x (Mm y) =
      starRingEnd ℂ (inner ℂ y (Mp x)))
    (hBound : ∀ x y, |(inner ℂ x (Mp y)).im| ≤
      C * ((inner ℂ x (G x)).re + (inner ℂ y (G y)).re))
    (hrec : ∀ n : ℤ,
      (((nu n)^2 : ℝ) : ℂ) •
        (M0 (c n) + Mp (c (n-1)) + Mm (c (n+1)) +
          (I * (gamma : ℂ)) • G (c n)) = H (c n))
    (hpoly : ∀ j : ℤ, ∃ A : ℝ, ∃ d : ℕ, ∀ N : ℕ,
      ptrSymMass (fun n => (inner ℂ (c (n+j)) (G (c (n+j)))).re) N
        ≤ A * (1 + (N : ℝ)) ^ d) :
    ∀ n, (inner ℂ (c n) (G (c n))).re = 0 :=
  ptr_passive_multimode_grade_spatial_loss_overlap_zero
    (fun _ => H) M0 Mp Mm G c nu gamma C hgamma hC hnu
    (fun _ x => hH x) hM0 hG hAdj hBound hrec hpoly

theorem ptr_factorized_helical_form_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F]
    (B : E →L[ℂ] F) (U : F →L[ℂ] F)
    (a : ℝ) (ha : 0 ≤ a) (hU : ‖U‖ ≤ 1) (x y : E) :
    |(inner ℂ x (((a : ℂ) • ((B.adjoint.comp U).comp B)) y)).im| ≤
      (a / 2) * ((inner ℂ x ((B.adjoint.comp B) x)).re +
        (inner ℂ y ((B.adjoint.comp B) y)).re) := by
  have hgx : (inner ℂ x ((B.adjoint.comp B) x)).re = ‖B x‖ ^ 2 := by
    rw [ContinuousLinearMap.comp_apply, B.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (B x)
  have hgy : (inner ℂ y ((B.adjoint.comp B) y)).re = ‖B y‖ ^ 2 := by
    rw [ContinuousLinearMap.comp_apply, B.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (B y)
  have hmp : inner ℂ x (((a : ℂ) • ((B.adjoint.comp U).comp B)) y) =
      (a : ℂ) * inner ℂ (B x) (U (B y)) := by
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      inner_smul_right, B.adjoint_inner_right]
  rw [hmp, Complex.im_ofReal_mul, hgx, hgy, abs_mul, abs_of_nonneg ha]
  have h1 := Complex.abs_im_le_norm (inner ℂ (B x) (U (B y)))
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (B x) (U (B y))
  have h3 := U.le_opNorm (B y)
  have h4 : ‖U (B y)‖ ≤ ‖B y‖ := by
    calc
      ‖U (B y)‖ ≤ ‖U‖ * ‖B y‖ := h3
      _ ≤ 1 * ‖B y‖ := mul_le_mul_of_nonneg_right hU (norm_nonneg _)
      _ = ‖B y‖ := one_mul _
  have h5 : |(inner ℂ (B x) (U (B y))).im| ≤ ‖B x‖ * ‖B y‖ :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_left h4 (norm_nonneg _)))
  calc
    a * |(inner ℂ (B x) (U (B y))).im|
        ≤ a * (‖B x‖ * ‖B y‖) :=
          mul_le_mul_of_nonneg_left h5 ha
    _ ≤ a * ((‖B x‖ ^ 2 + ‖B y‖ ^ 2) / 2) := by
      apply mul_le_mul_of_nonneg_left _ ha
      nlinarith [sq_nonneg (‖B x‖ - ‖B y‖)]
    _ = a / 2 * (‖B x‖ ^ 2 + ‖B y‖ ^ 2) := by ring

theorem ptr_factorized_helical_adjoint_pair
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F]
    (B : E →L[ℂ] F) (U : F →L[ℂ] F)
    (a : ℝ) (x y : E) :
    inner ℂ x (((a : ℂ) • ((B.adjoint.comp U.adjoint).comp B)) y) =
      starRingEnd ℂ
        (inner ℂ y (((a : ℂ) • ((B.adjoint.comp U).comp B)) x)) := by
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    inner_smul_right, B.adjoint_inner_right, U.adjoint_inner_right,
    map_mul, starRingEnd_apply]
  rw [show star (a : ℂ) = (a : ℂ) by simp]
  congr 1
  exact (inner_conj_symm (𝕜 := ℂ) (U (B x)) (B y)).symm

theorem ptr_factorized_multimode_tempered_loss_zero
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F]
    (H M0 : E →L[ℂ] E) (B : E →L[ℂ] F) (U : F →L[ℂ] F)
    (c : ℤ → E) (nu : ℤ → ℝ) (a gamma : ℝ)
    (ha : 0 < a) (hgamma : 0 < gamma) (hU : ‖U‖ ≤ 1)
    (hnu : ∀ n, nu n ≠ 0)
    (hH : ∀ x, (inner ℂ x (H x)).im = 0)
    (hM0 : ∀ x, (inner ℂ x (M0 x)).im = 0)
    (hrec : ∀ n : ℤ,
      (((nu n)^2 : ℝ) : ℂ) •
        (M0 (c n) +
          (((a : ℂ) • ((B.adjoint.comp U).comp B)) (c (n-1))) +
          (((a : ℂ) • ((B.adjoint.comp U.adjoint).comp B)) (c (n+1))) +
          (I * (gamma : ℂ)) • (B.adjoint.comp B) (c n)) = H (c n))
    (hpoly : ∀ j : ℤ, ∃ A : ℝ, ∃ d : ℕ, ∀ N : ℕ,
      ptrSymMass (fun n => ‖B (c (n+j))‖ ^ 2) N
        ≤ A * (1 + (N : ℝ)) ^ d) :
    ∀ n, B (c n) = 0 := by
  let G : E →L[ℂ] E := B.adjoint.comp B
  let Mp : E →L[ℂ] E := (a : ℂ) • ((B.adjoint.comp U).comp B)
  let Mm : E →L[ℂ] E := (a : ℂ) • ((B.adjoint.comp U.adjoint).comp B)
  have hg (x : E) : (inner ℂ x (G x)).re = ‖B x‖ ^ 2 := by
    dsimp [G]
    rw [B.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (B x)
  have hbound (x y : E) : |(inner ℂ x (Mp y)).im| ≤
      (a / 2) * ((inner ℂ x (G x)).re + (inner ℂ y (G y)).re) := by
    exact ptr_factorized_helical_form_bound B U a (le_of_lt ha) hU x y
  have hadj (x y : E) : inner ℂ x (Mm y) =
      starRingEnd ℂ (inner ℂ y (Mp x)) :=
    ptr_factorized_helical_adjoint_pair B U a x y
  have hpoly' : ∀ j : ℤ, ∃ A : ℝ, ∃ d : ℕ, ∀ N : ℕ,
      ptrSymMass
        (fun n => (inner ℂ (c (n+j)) (G (c (n+j)))).re) N
          ≤ A * (1 + (N : ℝ)) ^ d := by
    intro j
    obtain ⟨A,d,hh⟩ := hpoly j
    refine ⟨A,d,?_⟩
    intro N
    simpa only [hg] using hh N
  have hz := ptr_passive_multimode_tempered_loss_overlap_zero
    H.toLinearMap M0.toLinearMap Mp.toLinearMap Mm.toLinearMap G.toLinearMap
    c nu gamma (a / 2) hgamma (by positivity) hnu hH hM0
    (fun x => by change 0 ≤ (inner ℂ x (G x)).re; rw [hg]; positivity)
    hadj hbound hrec hpoly'
  intro n
  have hnorm : ‖B (c n)‖ ^ 2 = 0 := by
    have hh : (inner ℂ (c n) (G (c n))).re = 0 := hz n
    rwa [hg] at hh
  have : ‖B (c n)‖ = 0 := by nlinarith [norm_nonneg (B (c n))]
  exact norm_eq_zero.mp this

end RHTower
