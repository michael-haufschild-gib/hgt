import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer
import GaloisForLFunctions.RHTower.PhotonicPrimeCyclicSlabParabolicRealization
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Lossless temporal Maxwell stacks force real transfer zeros

A temporal slab of a lossless medium with impedance `κ > 0` and duration `τ > 0`
acts on the displacement/induction amplitudes of a plane wave of wavenumber `k`
by

  `T(κ, τ, k) = [[cos kτ, sin kτ / κ], [-κ sin kτ, cos kτ]]`.

At real `k` this is the corpus oscillator-slab flow. Along the slab the
amplitudes solve `u' = k [[0, 1/κ], [-κ, 0]] u`, and the temporal-Maxwell flux
`Q(u) = -2 Im(ū₀ u₁)` obeys `Q' = 2 Im k (κ |u₀|² + |u₁|²/κ)`. For `Im k > 0`
the flux therefore strictly increases through every slab, and through every
finite ordered stack of slabs. Starting from `e₀`, whose flux is zero, a stack
can never return to an amplitude with vanishing first component. Hence the
displacement entry `A(k)` of every lossless stack has no zeros off the real
wavenumber axis. It is even and entire.

For slab durations `log p`, the slab entries are `(p^{s-1/2} ± p^{1/2-s})/2` at
`k = -i(s - 1/2)`. So a lossless prime-log temporal stack has a transfer entry
that is a finite rational-power Dirichlet polynomial, and all its zeros lie on
`Re s = 1/2`.

Combined with the Hurwitz closed-locus transfer, this gives the PTR energy
receiver: if `XiC` is a locally uniform limit of nonzero multiples of lossless
temporal-stack entries, then RH holds. A lossless temporal medium forces
critical-line zeros; an off-line Xi zero would need gain or loss in every
approximating medium.
-/

open Complex Matrix Set Filter Topology
open scoped Matrix

namespace RHTower

/-- Transfer matrix of one lossless temporal slab of impedance `κ` and duration
`τ` at complex wavenumber `k`. -/
noncomputable def ptrLosslessSlab (κ τ : ℝ) (k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.cos (k * τ), Complex.sin (k * τ) / κ;
    -((κ : ℂ) * Complex.sin (k * τ)), Complex.cos (k * τ)]

/-- Ordered stack of lossless temporal slabs `(κ, τ)`; the last slab acts first. -/
noncomputable def ptrLosslessStack (L : List (ℝ × ℝ)) (k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (L.map fun x => ptrLosslessSlab x.1 x.2 k).prod

/-- Displacement entry of the stack transfer. -/
noncomputable def ptrLosslessStackEntry (L : List (ℝ × ℝ)) (k : ℂ) : ℂ :=
  ptrLosslessStack L k 0 0

/-- The temporal-Maxwell flux form on displacement/induction amplitudes. -/
noncomputable def ptrSlabFlux (v : Fin 2 → ℂ) : ℝ :=
  -2 * (starRingEnd ℂ (v 0) * v 1).im

/-- At real wavenumber the lossless slab is the corpus oscillator-slab flow. -/
theorem ptrLosslessSlab_ofReal (κ τ k : ℝ) :
    ptrLosslessSlab κ τ k = photonicOscillatorFlow κ (k * τ) := by
  unfold ptrLosslessSlab photonicOscillatorFlow
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← Complex.ofReal_mul, Complex.ofReal_cos,
    Complex.ofReal_sin, mul_comm]

private theorem im_star_mul_self_mul (a z : ℂ) :
    (starRingEnd ℂ z * (a * z)).im = a.im * Complex.normSq z := by
  rw [show starRingEnd ℂ z * (a * z) = a * (starRingEnd ℂ z * z) by ring, mul_comm
    ((starRingEnd ℂ) z) z, Complex.mul_conj]
  simp [Complex.mul_im]

private theorem im_star_mul_mul_self (a z : ℂ) :
    (starRingEnd ℂ (a * z) * z).im = -a.im * Complex.normSq z := by
  rw [map_mul, show starRingEnd ℂ a * starRingEnd ℂ z * z =
    starRingEnd ℂ a * (z * starRingEnd ℂ z) by ring, Complex.mul_conj]
  simp [Complex.mul_im]

/-- **Strict flux gain through a lossless slab.** For `Im k > 0` the temporal
Maxwell flux of every nonzero amplitude strictly increases across a slab of
positive impedance and duration. -/
theorem ptrSlabFlux_lt_slab {κ τ : ℝ} {k : ℂ} (hκ : 0 < κ) (hτ : 0 < τ) (hk : 0 < k.im)
    {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    ptrSlabFlux v < ptrSlabFlux ((ptrLosslessSlab κ τ k).mulVec v) := by
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  set u₀ : ℝ → ℂ := fun t => Complex.cos (k * t) * v 0 + Complex.sin (k * t) / κ * v 1
    with hu₀
  set u₁ : ℝ → ℂ := fun t => -((κ : ℂ) * Complex.sin (k * t)) * v 0 + Complex.cos (k * t) * v 1
    with hu₁
  have hlin : ∀ t : ℝ, HasDerivAt (fun y : ℝ => k * (y : ℂ)) k t := fun t => by
    simpa using ((hasDerivAt_id (t : ℂ)).const_mul k).comp_ofReal
  have hcos : ∀ t : ℝ, HasDerivAt (fun y : ℝ => Complex.cos (k * y))
      (-Complex.sin (k * t) * k) t := fun t => by
    have h := (Complex.hasDerivAt_cos (k * t)).comp t (hlin t)
    simpa [Function.comp_def] using h
  have hsin : ∀ t : ℝ, HasDerivAt (fun y : ℝ => Complex.sin (k * y))
      (Complex.cos (k * t) * k) t := fun t => by
    have h := (Complex.hasDerivAt_sin (k * t)).comp t (hlin t)
    simpa [Function.comp_def] using h
  have hd₀ : ∀ t, HasDerivAt u₀ (k / κ * u₁ t) t := by
    intro t
    have h := ((hcos t).mul_const (v 0)).add (((hsin t).div_const (κ : ℂ)).mul_const (v 1))
    refine h.congr_deriv ?_
    simp only [hu₁]
    field_simp
  have hd₁ : ∀ t, HasDerivAt u₁ (-(k * κ) * u₀ t) t := by
    intro t
    have h := (((hsin t).const_mul (κ : ℂ)).neg.mul_const (v 0)).add ((hcos t).mul_const (v 1))
    refine h.congr_deriv ?_
    simp only [hu₀]
    field_simp
    ring
  set f : ℝ → ℝ := fun t => -2 * (starRingEnd ℂ (u₀ t) * u₁ t).im with hf
  set f' : ℝ → ℝ := fun t =>
    2 * k.im * (κ * Complex.normSq (u₀ t) + Complex.normSq (u₁ t) / κ) with hf'
  have hfd : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    have hprod := ((hd₀ t).star).mul (hd₁ t)
    have him := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hprod).const_mul (-2 : ℝ)
    refine him.congr_deriv ?_
    simp only [Complex.imCLM_apply, hf']
    rw [Complex.add_im, show star (k / κ * u₁ t) = starRingEnd ℂ (k / κ * u₁ t) from rfl,
      im_star_mul_mul_self, show star (u₀ t) = starRingEnd ℂ (u₀ t) from rfl,
      im_star_mul_self_mul]
    have hdiv : (k / (κ : ℂ)).im = k.im / κ := by
      rw [Complex.div_ofReal_im]
    have hmul : (-(k * (κ : ℂ))).im = -(k.im * κ) := by
      simp [Complex.mul_im]
    rw [hdiv, hmul]
    field_simp
    ring
  have hinv : ∀ t : ℝ,
      v 0 = Complex.cos (k * t) * u₀ t - Complex.sin (k * t) / κ * u₁ t ∧
      v 1 = (κ : ℂ) * Complex.sin (k * t) * u₀ t + Complex.cos (k * t) * u₁ t := by
    intro t
    have hcs := Complex.cos_sq_add_sin_sq (k * (t : ℂ))
    constructor
    · simp only [hu₀, hu₁]
      field_simp
      linear_combination (-(κ : ℂ) * v 0) * hcs
    · simp only [hu₀, hu₁]
      field_simp
      linear_combination (-(v 1)) * hcs
  have hpos : ∀ t, 0 < f' t := by
    intro t
    have hne : u₀ t ≠ 0 ∨ u₁ t ≠ 0 := by
      by_contra h
      push Not at h
      apply hv
      ext i
      fin_cases i
      · simp [(hinv t).1, h.1, h.2]
      · simp [(hinv t).2, h.1, h.2]
    have h0 : 0 ≤ Complex.normSq (u₀ t) := Complex.normSq_nonneg _
    have h1 : 0 ≤ Complex.normSq (u₁ t) := Complex.normSq_nonneg _
    have hsum : 0 < κ * Complex.normSq (u₀ t) + Complex.normSq (u₁ t) / κ := by
      rcases hne with h | h
      · have := Complex.normSq_pos.mpr h
        have : 0 < κ * Complex.normSq (u₀ t) := mul_pos hκ this
        positivity
      · have := Complex.normSq_pos.mpr h
        have : 0 < Complex.normSq (u₁ t) / κ := div_pos this hκ
        positivity
    simp only [hf']
    positivity
  have hmono : StrictMonoOn f (Icc 0 τ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 τ)
    · exact fun t _ => (hfd t).continuousAt.continuousWithinAt
    · intro t _
      rw [(hfd t).deriv]
      exact hpos t
  have hlt := hmono (left_mem_Icc.mpr hτ.le) (right_mem_Icc.mpr hτ.le) hτ
  have hf0 : f 0 = ptrSlabFlux v := by
    simp [hf, hu₀, hu₁, ptrSlabFlux]
  have hfτ : f τ = ptrSlabFlux ((ptrLosslessSlab κ τ k).mulVec v) := by
    simp only [hf, hu₀, hu₁, ptrSlabFlux, ptrLosslessSlab, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    simp
    try ring_nf
  rw [← hf0, ← hfτ]
  exact hlt

/-- The flux never decreases across a lossless slab when `Im k > 0`. -/
theorem ptrSlabFlux_le_slab {κ τ : ℝ} {k : ℂ} (hκ : 0 < κ) (hτ : 0 < τ) (hk : 0 < k.im)
    (v : Fin 2 → ℂ) :
    ptrSlabFlux v ≤ ptrSlabFlux ((ptrLosslessSlab κ τ k).mulVec v) := by
  by_cases hv : v = 0
  · subst hv; simp
  · exact (ptrSlabFlux_lt_slab hκ hτ hk hv).le

/-- **Strict flux gain through a lossless stack.** -/
theorem ptrSlabFlux_lt_stack {L : List (ℝ × ℝ)} {k : ℂ}
    (hL : ∀ x ∈ L, 0 < x.1 ∧ 0 < x.2) (hne : L ≠ []) (hk : 0 < k.im)
    {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    ptrSlabFlux v < ptrSlabFlux ((ptrLosslessStack L k).mulVec v) := by
  induction L with
  | nil => exact absurd rfl hne
  | cons x L ih =>
    have hx := hL x (List.mem_cons_self ..)
    have hL' : ∀ y ∈ L, 0 < y.1 ∧ 0 < y.2 := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    rw [ptrLosslessStack, List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
    by_cases hnil : L = []
    · subst hnil
      simpa [ptrLosslessStack] using ptrSlabFlux_lt_slab hx.1 hx.2 hk hv
    · exact lt_of_lt_of_le (ih hL' hnil) (ptrSlabFlux_le_slab hx.1 hx.2 hk _)

/-- Each lossless stack displacement entry is nonzero in the open upper half-plane. -/
theorem ptrLosslessStackEntry_ne_zero_of_im_pos {L : List (ℝ × ℝ)} {k : ℂ}
    (hL : ∀ x ∈ L, 0 < x.1 ∧ 0 < x.2) (hk : 0 < k.im) :
    ptrLosslessStackEntry L k ≠ 0 := by
  by_cases hnil : L = []
  · subst hnil
    simp [ptrLosslessStackEntry, ptrLosslessStack]
  intro hzero
  have hv : (![1, 0] : Fin 2 → ℂ) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hlt := ptrSlabFlux_lt_stack hL hnil hk hv
  have h0 : ptrSlabFlux ![1, 0] = 0 := by simp [ptrSlabFlux]
  have hM : ptrSlabFlux ((ptrLosslessStack L k).mulVec ![1, 0]) = 0 := by
    have hentry : ((ptrLosslessStack L k).mulVec ![1, 0]) 0 = 0 := by
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simpa [ptrLosslessStackEntry] using hzero
    simp [ptrSlabFlux, hentry]
  rw [h0, hM] at hlt
  exact lt_irrefl _ hlt

private noncomputable def ptrSignFlip : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

private theorem ptrSignFlip_mul_self : ptrSignFlip * ptrSignFlip = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ptrSignFlip, Matrix.mul_apply]

private theorem ptrLosslessSlab_neg (κ τ : ℝ) (k : ℂ) :
    ptrLosslessSlab κ τ (-k) = ptrSignFlip * ptrLosslessSlab κ τ k * ptrSignFlip := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptrLosslessSlab, ptrSignFlip, Matrix.mul_apply, Fin.sum_univ_two, neg_mul,
      Complex.cos_neg, Complex.sin_neg, neg_div]

private theorem ptrLosslessStack_neg (L : List (ℝ × ℝ)) (k : ℂ) :
    ptrLosslessStack L (-k) = ptrSignFlip * ptrLosslessStack L k * ptrSignFlip := by
  induction L with
  | nil => simp [ptrLosslessStack, ptrSignFlip_mul_self]
  | cons x L ih =>
    simp only [ptrLosslessStack, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, ptrLosslessSlab_neg]
    calc ptrSignFlip * ptrLosslessSlab x.1 x.2 k * ptrSignFlip *
          (ptrSignFlip * (List.map (fun x => ptrLosslessSlab x.1 x.2 k) L).prod * ptrSignFlip)
        = ptrSignFlip * ptrLosslessSlab x.1 x.2 k * (ptrSignFlip * ptrSignFlip) *
          (List.map (fun x => ptrLosslessSlab x.1 x.2 k) L).prod * ptrSignFlip := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ptrSignFlip_mul_self, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-- The stack displacement entry is even in the wavenumber. -/
theorem ptrLosslessStackEntry_neg (L : List (ℝ × ℝ)) (k : ℂ) :
    ptrLosslessStackEntry L (-k) = ptrLosslessStackEntry L k := by
  rw [ptrLosslessStackEntry, ptrLosslessStack_neg, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [ptrSignFlip, ptrLosslessStackEntry]

/-- **Real-zero law of lossless temporal stacks.** Every zero of the displacement
entry of a finite stack of lossless temporal slabs lies on the real wavenumber
axis. -/
theorem ptrLosslessStackEntry_zero_im_eq_zero {L : List (ℝ × ℝ)}
    (hL : ∀ x ∈ L, 0 < x.1 ∧ 0 < x.2) {k : ℂ} (hzero : ptrLosslessStackEntry L k = 0) :
    k.im = 0 := by
  rcases lt_trichotomy k.im 0 with h | h | h
  · have hneg : 0 < (-k).im := by simp; linarith
    have := ptrLosslessStackEntry_ne_zero_of_im_pos hL hneg
    rw [ptrLosslessStackEntry_neg] at this
    exact absurd hzero this
  · exact h
  · exact absurd hzero (ptrLosslessStackEntry_ne_zero_of_im_pos hL h)

/-- Every entry of a lossless stack is entire in the wavenumber. -/
theorem ptrLosslessStack_differentiable (L : List (ℝ × ℝ)) (i j : Fin 2) :
    Differentiable ℂ (fun k => ptrLosslessStack L k i j) := by
  induction L generalizing i j with
  | nil =>
    simp only [ptrLosslessStack, List.map_nil, List.prod_nil]
    exact differentiable_const _
  | cons x L ih =>
    have hs : Differentiable ℂ (fun k : ℂ => Complex.sin (k * x.2)) :=
      Complex.differentiable_sin.comp (differentiable_id.mul_const _)
    have hslab : ∀ a b : Fin 2, Differentiable ℂ (fun k => ptrLosslessSlab x.1 x.2 k a b) := by
      intro a b
      fin_cases a <;> fin_cases b
      · simp [ptrLosslessSlab]
      · simpa [ptrLosslessSlab] using hs.div_const _
      · simpa [ptrLosslessSlab] using (hs.const_mul ((x.1 : ℂ))).neg
      · simp [ptrLosslessSlab]
    simp only [ptrLosslessStack, List.map_cons, List.prod_cons, Matrix.mul_apply,
      Fin.sum_univ_two]
    exact ((hslab i 0).mul (ih 0 j)).add ((hslab i 1).mul (ih 1 j))

/-- For slab duration `log p`, the slab entries at `k = -i(s - 1/2)` are the
symmetric half-density Euler combinations `(p^{s-1/2} ± p^{1/2-s})/2`. -/
theorem ptrLosslessSlab_primeLog (p : Nat.Primes) (s : ℂ) :
    Complex.cos (-(Complex.I * (s - 1 / 2)) * (Real.log ((p : ℕ) : ℝ) : ℂ)) =
      (((p : ℕ) : ℂ) ^ (s - 1 / 2) + ((p : ℕ) : ℂ) ^ (-(s - 1 / 2))) / 2 ∧
    Complex.sin (-(Complex.I * (s - 1 / 2)) * (Real.log ((p : ℕ) : ℝ) : ℂ)) =
      -(Complex.I * ((((p : ℕ) : ℂ) ^ (s - 1 / 2) - ((p : ℕ) : ℂ) ^ (-(s - 1 / 2))) / 2)) := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hlog : (Real.log ((p : ℕ) : ℝ) : ℂ) = Complex.log ((p : ℕ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity), Complex.ofReal_natCast]
  rw [Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hp0, hlog]
  set w := Complex.log ((p : ℕ) : ℂ) * (s - 1 / 2) with hw
  have harg : -(Complex.I * (s - 1 / 2)) * Complex.log ((p : ℕ) : ℂ) = -(w * Complex.I) := by
    rw [hw]; ring
  have harg' : Complex.log ((p : ℕ) : ℂ) * -(s - 1 / 2) = -w := by rw [hw]; ring
  rw [harg, harg', Complex.cos_neg, Complex.sin_neg, Complex.cos, Complex.sin]
  constructor
  · congr 1
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  · have e1 : -(w * Complex.I) * Complex.I = w := by
      rw [neg_mul, mul_assoc, Complex.I_mul_I]; ring
    have e2 : w * Complex.I * Complex.I = -w := by
      rw [mul_assoc, Complex.I_mul_I]; ring
    rw [e1, e2]
    ring

/-- **Critical-line law of lossless prime-log temporal stacks.** If every slab
has positive impedance and a prime-logarithm duration, the stack entry, read at
`k = -i(s - 1/2)`, vanishes only on `Re s = 1/2`. -/
theorem ptrLosslessPrimeLogStack_zero_re_eq_half (L : List (ℝ × Nat.Primes))
    (hL : ∀ x ∈ L, 0 < x.1) {s : ℂ}
    (hzero : ptrLosslessStackEntry (L.map fun x => (x.1, Real.log ((x.2 : ℕ) : ℝ)))
      (-(Complex.I * (s - 1 / 2))) = 0) :
    s.re = 1 / 2 := by
  have hL' : ∀ x ∈ L.map (fun x => (x.1, Real.log ((x.2 : ℕ) : ℝ))), 0 < x.1 ∧ 0 < x.2 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ⟨hL y hy, Real.log_pos (by exact_mod_cast y.2.property.one_lt)⟩
  have him := ptrLosslessStackEntry_zero_im_eq_zero hL' hzero
  have : (-(Complex.I * (s - 1 / 2))).im = -(s.re - 1 / 2) := by simp
  rw [this] at him
  linarith

/-- **PTR energy receiver.** If the completed Xi function is a locally uniform
limit of nonzero multiples of displacement entries of lossless temporal Maxwell
stacks, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_XiC_limit_of_losslessTemporalStacks
    (L : ℕ → List (ℝ × ℝ)) (c : ℕ → ℂ)
    (hL : ∀ n, ∀ x ∈ L n, 0 < x.1 ∧ 0 < x.2) (hc : ∀ n, c n ≠ 0)
    (hconv : TendstoLocallyUniformly (fun n k => c n * ptrLosslessStackEntry (L n) k)
      XiC atTop) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants hconv
  · exact Eventually.of_forall fun n =>
      (ptrLosslessStack_differentiable (L n) 0 0).const_mul (c n)
  · refine Eventually.of_forall fun n z hz => ?_
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (hc n)
    · exact ptrLosslessStackEntry_zero_im_eq_zero (hL n) h

end RHTower
