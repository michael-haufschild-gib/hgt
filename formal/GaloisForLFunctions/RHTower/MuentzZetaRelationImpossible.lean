import GaloisForLFunctions.RHTower.BorderDeterminantVanishing
import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowIndependence

/-!
# No Müntz system inverts zeta, so every finite section is obstructed

`BorderDeterminantVanishing` reduces the last escape route of a finite Báez-Duarte section to a single
identity on the strip: coefficients `c`, not all zero, with

`(∑ᵢ cᵢ(θᵢ^s − θᵢ))·ζ(s) = c_N` for every `s` with `½ < Re s < 1`.

This file refutes it, for distinct dilations in `(0,1)`, and the refutation is elementary.

* `eq_zero_of_forall_sum_cpow_eq` — the concrete form of Dedekind's independence of characters: if
  `∑ᵢ bᵢ·θᵢ^s = K` for **all** `s`, with the `θᵢ` distinct, positive and `≠ 1`, then all `bᵢ` and `K`
  vanish.  Proved from `linearIndependent_monoidHom` through the corpus's `logCpowChar`;
* **`eq_zero_of_muentz_zeta_relation`** — the identity above forces `c = 0`.  The combination is entire and
  `ζ` is analytic on the convex half-plane `Re s < 1`, so the identity theorem propagates the relation from
  the strip to that half-plane; the trivial zero `ζ(−2) = 0` then kills `c_N`, `ζ(3/4) ≠ 0` kills the
  combination near `3/4` and hence everywhere, and the character independence finishes;
* **`bdDist_pos_of_injective_of_lt_one`** — consequently every finite family of distinct dilations in
  `(0,1)` has positive Báez-Duarte distance.

The last statement is the structural form of what the corpus previously knew only for special families
(`bdDistDiscrete_pos` by a factorial floor, `bdDist_single_ge` for one generator): no finite section can be
dense, for *arithmetic-free* reasons — a finite Müntz system cannot invert `ζ`.
-/

open Complex Set Filter Topology

noncomputable section

namespace RHTower

/-! ## Characters: the concrete independence statement -/

/-- A finite exponential sum in `s`, written with `exp` so that differentiability is automatic. -/
def muentzSum {N : ℕ} (θ : Fin N → ℝ) (b : Fin N → ℂ) (s : ℂ) : ℂ :=
  ∑ i, b i * Complex.exp (s * ((Real.log (θ i) : ℝ) : ℂ))

theorem muentzSum_eq_cpow {N : ℕ} (θ : Fin N → ℝ) (hθ0 : ∀ i, 0 < θ i) (b : Fin N → ℂ) (s : ℂ) :
    muentzSum θ b s = ∑ i, b i * ((θ i : ℝ) : ℂ) ^ s := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (s * ((Real.log (θ i) : ℝ) : ℂ)) = -(-s) * ((Real.log (θ i) : ℝ) : ℂ) by ring,
    exp_neg_mul_log_eq_cpow (hθ0 i), neg_neg]

theorem differentiable_muentzSum {N : ℕ} (θ : Fin N → ℝ) (b : Fin N → ℂ) :
    Differentiable ℂ (muentzSum θ b) := by
  show Differentiable ℂ fun s => ∑ i, b i * Complex.exp (s * ((Real.log (θ i) : ℝ) : ℂ))
  fun_prop

/-- **Dedekind's independence of characters, concretely.**  An exponential sum in distinct positive bases,
none equal to `1`, that is constant in `s` has vanishing coefficients and vanishing constant. -/
theorem eq_zero_of_forall_sum_cpow_eq {N : ℕ} (θ : Fin N → ℝ) (hθ0 : ∀ i, 0 < θ i)
    (hθ1 : ∀ i, θ i ≠ 1) (hinj : Function.Injective θ) (b : Fin N → ℂ) (K : ℂ)
    (h : ∀ s : ℂ, ∑ i, b i * ((θ i : ℝ) : ℂ) ^ s = K) :
    (∀ i, b i = 0) ∧ K = 0 := by
  classical
  have hLI : LinearIndependent ℂ
      (fun f : Multiplicative ℂ →* ℂ => (f : Multiplicative ℂ → ℂ)) :=
    linearIndependent_monoidHom (Multiplicative ℂ) ℂ
  set ψ : Option (Fin N) → (Multiplicative ℂ →* ℂ) :=
    fun j => Option.rec (logCpowChar (Real.log 1)) (fun i => logCpowChar (Real.log (θ i))) j with hψ
  have hψinj : Function.Injective ψ := by
    intro j1 j2 hj
    match j1, j2 with
    | none, none => rfl
    | none, some i => exact absurd (logCpowChar_injective one_pos (hθ0 i) hj) (Ne.symm (hθ1 i))
    | some i, none => exact absurd (logCpowChar_injective (hθ0 i) one_pos hj) (hθ1 i)
    | some i1, some i2 => exact congrArg some (hinj (logCpowChar_injective (hθ0 i1) (hθ0 i2) hj))
  have hcomp := hLI.comp ψ hψinj
  rw [Fintype.linearIndependent_iff] at hcomp
  set lam : Option (Fin N) → ℂ := fun j => Option.rec (-K) b j with hlam
  have hrel : ∑ j : Option (Fin N), lam j •
      ((fun f : Multiplicative ℂ →* ℂ => (f : Multiplicative ℂ → ℂ)) ∘ ψ) j = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply]
    rw [Fintype.sum_option]
    have hone : (ψ none) m = 1 := by
      show logCpowChar (Real.log 1) m = 1
      rw [logCpowChar_apply, Real.log_one]
      simp
    have hsome : ∀ i : Fin N, (ψ (some i)) m = ((θ i : ℝ) : ℂ) ^ (-(Multiplicative.toAdd m)) := by
      intro i
      show logCpowChar (Real.log (θ i)) m = _
      rw [logCpowChar_apply, ← exp_neg_mul_log_eq_cpow (hθ0 i)]
    have hval := h (-(Multiplicative.toAdd m))
    show lam none * (ψ none) m + ∑ i : Fin N, lam (some i) * (ψ (some i)) m = 0
    have hlamnone : lam none = -K := rfl
    have hlamsome : ∀ i : Fin N, lam (some i) = b i := fun _ => rfl
    rw [hone, hlamnone]
    simp only [hsome, hlamsome, mul_one]
    linear_combination hval
  refine ⟨fun i => hcomp lam hrel (some i), ?_⟩
  have hnone : (-K : ℂ) = 0 := hcomp lam hrel none
  exact neg_eq_zero.mp hnone

/-! ## The relation on the strip is impossible -/

/-- **No finite Müntz system inverts `ζ` on the strip.**  For distinct dilations in `(0,1)` the only
coefficient vector satisfying `(∑ᵢ cᵢ(θᵢ^s − θᵢ))·ζ(s) = c_N` throughout the strip is zero. -/
theorem eq_zero_of_muentz_zeta_relation {N : ℕ} (θ : Fin N → ℝ)
    (hθ0 : ∀ i, 0 < θ i) (hθ1 : ∀ i, θ i < 1) (hinj : Function.Injective θ)
    (c : Fin (N + 1) → ℂ)
    (hrel : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      (∑ i : Fin N, c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ))) * riemannZeta s
        = c (Fin.last N)) :
    ∀ j, c j = 0 := by
  classical
  set b : Fin N → ℂ := fun i => c i.castSucc with hb
  set K : ℂ := ∑ i : Fin N, c i.castSucc * ((θ i : ℝ) : ℂ) with hK
  -- the combination, as an entire function
  set P : ℂ → ℂ := fun s => muentzSum θ b s - K with hP
  have hPdiff : Differentiable ℂ P := by
    rw [hP]
    exact (differentiable_muentzSum θ b).sub_const K
  have hPeq : ∀ s : ℂ,
      P s = ∑ i : Fin N, c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ)) := by
    intro s
    show muentzSum θ b s - K = _
    rw [muentzSum_eq_cpow θ hθ0 b s, hK, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hb]; ring
  -- the half-plane where zeta is analytic
  set U : Set ℂ := {s : ℂ | s.re < 1} with hU
  have hUopen : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hUconv : Convex ℝ U := convex_halfSpace_re_lt 1
  have hHan : AnalyticOnNhd ℂ (fun s => P s * riemannZeta s - c (Fin.last N)) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUopen
    have hs1 : s ≠ 1 := by
      intro h
      rw [hU, Set.mem_setOf_eq, h, Complex.one_re] at hs
      norm_num at hs
    exact (((hPdiff s).mul (differentiableAt_riemannZeta hs1)).sub_const
      (c (Fin.last N))).differentiableWithinAt
  -- the relation holds near 3/4, hence on the whole half-plane
  set w₀ : ℂ := ((3 / 4 : ℝ) : ℂ) with hw₀
  have hw₀re : w₀.re = 3 / 4 := Complex.ofReal_re _
  have hw₀U : w₀ ∈ U := by
    rw [hU, Set.mem_setOf_eq, hw₀re]
    norm_num
  have hevlo : ∀ᶠ s in 𝓝 w₀, 1 / 2 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).eventually_mem
      (by show (1 : ℝ) / 2 < w₀.re; rw [hw₀re]; norm_num)
  have hevhi : ∀ᶠ s in 𝓝 w₀, s.re < 1 :=
    (isOpen_lt Complex.continuous_re continuous_const).eventually_mem
      (by show w₀.re < (1 : ℝ); rw [hw₀re]; norm_num)
  have hHzero : (fun s => P s * riemannZeta s - c (Fin.last N)) =ᶠ[𝓝 w₀] 0 := by
    filter_upwards [hevlo, hevhi] with s h2 h3
    rw [hPeq s, hrel s h2 h3, sub_self]
    rfl
  have hall : Set.EqOn (fun s => P s * riemannZeta s - c (Fin.last N)) 0 U :=
    hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconv.isPreconnected hw₀U hHzero
  -- the trivial zero kills the constant
  have hlast : c (Fin.last N) = 0 := by
    have hmem : ((-2 : ℂ)) ∈ U := by
      rw [hU, Set.mem_setOf_eq]
      norm_num
    have h2 := hall hmem
    have hz : riemannZeta (-2 : ℂ) = 0 := by
      have := riemannZeta_neg_two_mul_nat_add_one 0
      norm_num at this
      exact this
    simp only [hz, mul_zero, zero_sub, Pi.zero_apply, neg_eq_zero] at h2
    exact h2
  -- zeta does not vanish near 3/4, so the combination vanishes there and hence everywhere
  have hz₀ : riemannZeta w₀ ≠ 0 :=
    riemannZeta_ne_zero_of_ofReal_mem_Ioo (by norm_num) (by norm_num)
  have hne1 : w₀ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hw₀re
    norm_num at hw₀re
  have hevz : ∀ᶠ s in 𝓝 w₀, riemannZeta s ≠ 0 :=
    ((differentiableAt_riemannZeta hne1).continuousAt).eventually_ne hz₀
  have hPzero : P =ᶠ[𝓝 w₀] 0 := by
    filter_upwards [hevz, hevhi] with s hzs hUs
    have hmem : s ∈ U := by rw [hU, Set.mem_setOf_eq]; exact hUs
    have h0 := hall hmem
    simp only [Pi.zero_apply, hlast, sub_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_right hzs
  have hPan : AnalyticOnNhd ℂ P Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hPdiff
  have hPall : Set.EqOn P 0 Set.univ :=
    hPan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ w₀) hPzero
  -- character independence
  have hsum : ∀ s : ℂ, ∑ i : Fin N, b i * ((θ i : ℝ) : ℂ) ^ s = K := by
    intro s
    have h0 : P s = 0 := hPall (Set.mem_univ s)
    have h1 : muentzSum θ b s - K = 0 := h0
    rw [← muentzSum_eq_cpow θ hθ0 b s]
    exact sub_eq_zero.mp h1
  obtain ⟨hbz, -⟩ :=
    eq_zero_of_forall_sum_cpow_eq θ hθ0 (fun i => ne_of_lt (hθ1 i)) hinj b K hsum
  intro j
  refine Fin.lastCases ?_ ?_ j
  · exact hlast
  · intro i
    exact hbz i

/-! ## The capstone -/

/-- **The pairing functions are independent.**  For distinct dilations in `(0,1)` the sampled generator and
target pairings are linearly independent as functions on the strip — the hypothesis the abstract obstruction
consumes. -/
theorem linearIndependent_borderRowFun_of_injective {N : ℕ} (θ : Fin N → ℝ)
    (hθ0 : ∀ i, 0 < θ i) (hθ1 : ∀ i, θ i < 1) (hinj : Function.Injective θ) :
    LinearIndependent ℂ (borderRowFun θ) := by
  by_contra h
  obtain ⟨c, ⟨i₀, hi₀⟩, hrel⟩ := muentz_relation_of_not_linearIndependent θ h
  exact hi₀ (eq_zero_of_muentz_zeta_relation θ hθ0 hθ1 hinj c hrel i₀)

/-- **No finite section of distinct dilations is dense.**  Every finite family of distinct dilations in
`(0,1)` has strictly positive Báez-Duarte distance — unconditionally, and with no arithmetic input: a
finite Müntz system cannot invert `ζ`. -/
theorem bdDist_pos_of_injective_of_lt_one {N : ℕ} (θ : Fin N → ℝ)
    (hθ0 : ∀ i, 0 < θ i) (hθ1 : ∀ i, θ i < 1) (hinj : Function.Injective θ) :
    0 < bdDist θ :=
  bdDist_pos_of_linearIndependent_borderRowFun θ (fun i => ⟨hθ0 i, (hθ1 i).le⟩)
    (linearIndependent_borderRowFun_of_injective θ hθ0 hθ1 hinj)

end RHTower

end
