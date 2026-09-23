import GaloisForLFunctions.RHTower.C5FrozenJetTaylorBounds

/-!
# The frozen-jet growth bound (stages 2–3)

For a `C⁵` chain `c → c₁ → … → c₅` with primitive `σ` (`σ' = c`), centre `u` and radius `t`, set

* `e s = (c(u+s) + c(u−s))/2`, `o s = (c(u+s) − c(u−s))/2` (and their derivatives `e₁, o₁, e₂, o₂`),
* `E t = (σ(u+t) − σ(u−t))/2 = ∫₀ᵗ e`, `O t = (σ(u+t) + σ(u−t))/2 − σ u = ∫₀ᵗ o`,
* `N = o·tE − O(E + te)`, `M = o₁·tE − O(2e + te₁)` (so `N' = M`), `ε = tM − 5N`.

With the frozen jets `c₀ … c₃` at `u` and sup-norms `S₄, S₅` of `c₄, c₅` on `[u−t, u+t]`, the
truncated polynomial parts of `tM` and `5N` cancel exactly, and

```text
ε = E·K₁ + O·K₂,   K₁ = t²o₁ − 5to + 8O,   K₂ = 3te − 3E − t²e₁,
|K₁| ≤ (2/45) S₅ t⁶,   |K₂| ≤ (2/15) S₄ t⁵,
N = E·Λ − O·Y,   Λ = to − 2O,   Y = te − E,
|Λ − c₃t⁴/12| ≤ S₅t⁶/180,   |Y − c₂t³/3| ≤ S₄t⁵/30,
|E − c₀t − c₂t³/6| ≤ S₄t⁵/120,   |O − c₁t²/2 − c₃t⁴/24| ≤ S₅t⁶/720.
```

All bounds come from the monotone comparison lemma of stage 1 applied to closed-form
auxiliaries whose derivatives are the kernels.
-/

open Set

namespace RHTower

section

variable {c c₁ c₂ c₃ c₄ c₅ σ : ℝ → ℝ} {u t S₄ S₅ : ℝ}

/-- Even and odd parts of `c` around `u`, and their derivatives. -/
noncomputable def fjEven (c : ℝ → ℝ) (u s : ℝ) : ℝ := (c (u + s) + c (u - s)) / 2
noncomputable def fjOdd (c : ℝ → ℝ) (u s : ℝ) : ℝ := (c (u + s) - c (u - s)) / 2

/-- The primitives `E`, `O`. -/
noncomputable def fjE (σ : ℝ → ℝ) (u t : ℝ) : ℝ := (σ (u + t) - σ (u - t)) / 2
noncomputable def fjO (σ : ℝ → ℝ) (u t : ℝ) : ℝ := (σ (u + t) + σ (u - t)) / 2 - σ u

theorem hasDerivAt_fjEven (hc : ∀ x, HasDerivAt c (c₁ x) x) (u s : ℝ) :
    HasDerivAt (fjEven c u) (fjOdd c₁ u s) s := by
  have hp := (hc (u + s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hc (u - s)).comp s ((hasDerivAt_id s).const_sub u)
  have := (hp.add hm).div_const 2
  unfold fjEven fjOdd
  convert this using 1 <;> first | rfl | ((try simp only [Pi.add_apply, Function.comp_apply, id_eq]); ring)

theorem hasDerivAt_fjOdd (hc : ∀ x, HasDerivAt c (c₁ x) x) (u s : ℝ) :
    HasDerivAt (fjOdd c u) (fjEven c₁ u s) s := by
  have hp := (hc (u + s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hc (u - s)).comp s ((hasDerivAt_id s).const_sub u)
  have := (hp.sub hm).div_const 2
  unfold fjEven fjOdd
  convert this using 1 <;> first | rfl | ((try simp only [Pi.sub_apply, Function.comp_apply, id_eq]); ring)

theorem hasDerivAt_fjE (hσ : ∀ x, HasDerivAt σ (c x) x) (u t : ℝ) :
    HasDerivAt (fjE σ u) (fjEven c u t) t := by
  have hp := (hσ (u + t)).comp t ((hasDerivAt_id t).const_add u)
  have hm := (hσ (u - t)).comp t ((hasDerivAt_id t).const_sub u)
  have := (hp.sub hm).div_const 2
  unfold fjE fjEven
  convert this using 1 <;> first | rfl | ((try simp only [Pi.sub_apply, Function.comp_apply, id_eq]); ring)

theorem hasDerivAt_fjO (hσ : ∀ x, HasDerivAt σ (c x) x) (u t : ℝ) :
    HasDerivAt (fjO σ u) (fjOdd c u t) t := by
  have hp := (hσ (u + t)).comp t ((hasDerivAt_id t).const_add u)
  have hm := (hσ (u - t)).comp t ((hasDerivAt_id t).const_sub u)
  have := ((hp.add hm).div_const 2).sub_const (σ u)
  unfold fjO fjOdd
  convert this using 1 <;> first | rfl | ((try simp only [Pi.add_apply, Function.comp_apply, id_eq]); ring)

theorem fjE_zero (σ : ℝ → ℝ) (u : ℝ) : fjE σ u 0 = 0 := by simp [fjE]
theorem fjO_zero (σ : ℝ → ℝ) (u : ℝ) : fjO σ u 0 = 0 := by simp [fjO]
theorem fjOdd_zero (c : ℝ → ℝ) (u : ℝ) : fjOdd c u 0 = 0 := by simp [fjOdd]
theorem fjEven_zero (c : ℝ → ℝ) (u : ℝ) : fjEven c u 0 = c u := by simp [fjEven]

/-- Pointwise bounds on the even/odd data on `[0, t]` from the frozen-jet expansions. -/
theorem fj_pointwise_bounds (ht : 0 ≤ t)
    (hc : ∀ x, HasDerivAt c (c₁ x) x) (hc₁ : ∀ x, HasDerivAt c₁ (c₂ x) x)
    (hc₂ : ∀ x, HasDerivAt c₂ (c₃ x) x) (hc₃ : ∀ x, HasDerivAt c₃ (c₄ x) x)
    (hc₄ : ∀ x, HasDerivAt c₄ (c₅ x) x)
    (hS₄ : ∀ x ∈ Icc (u - t) (u + t), |c₄ x| ≤ S₄) (hS₅ : ∀ x ∈ Icc (u - t) (u + t), |c₅ x| ≤ S₅) :
    ∀ s ∈ Icc (0 : ℝ) t,
      |fjEven c u s - (c u + c₂ u * s ^ (2 : ℕ) / 2)| ≤ S₄ * s ^ (4 : ℕ) / 24 ∧
      |fjOdd c u s - (c₁ u * s + c₃ u * s ^ (3 : ℕ) / 6)| ≤ S₅ * s ^ (5 : ℕ) / 120 ∧
      |fjOdd c₁ u s - c₂ u * s| ≤ S₄ * s ^ (3 : ℕ) / 6 ∧
      |fjEven c₁ u s - (c₁ u + c₃ u * s ^ (2 : ℕ) / 2)| ≤ S₅ * s ^ (4 : ℕ) / 24 ∧
      |fjEven c₂ u s - c₂ u| ≤ S₄ * s ^ (2 : ℕ) / 2 ∧
      |fjOdd c₂ u s - c₃ u * s| ≤ S₅ * s ^ (3 : ℕ) / 6 := by
  have h4 := frozenJet_bounds_four ht hc hc₁ hc₂ hc₃ hS₄
  have h5 := frozenJet_bounds_four ht hc₁ hc₂ hc₃ hc₄ hS₅
  -- fifth-order expansion of `c` with `S₅`
  have h5c := abs_le_pow_div_of_abs_deriv_le_Icc
    (h := fun s => c (u + s) - (c u + c₁ u * s + c₂ u * s ^ (2 : ℕ) / 2 + c₃ u * s ^ (3 : ℕ) / 6 +
      c₄ u * s ^ (4 : ℕ) / 24))
    (h' := fun s => c₁ (u + s) - (c₁ u + c₂ u * s + c₃ u * s ^ (2 : ℕ) / 2 + c₄ u * s ^ (3 : ℕ) / 6))
    (K := S₅ / 24) (k := 4) ht (by simp) ?_ ?_
  rotate_left
  · intro s _
    have hp : HasDerivAt (fun s : ℝ => c u + c₁ u * s + c₂ u * s ^ (2 : ℕ) / 2 + c₃ u * s ^ (3 : ℕ) / 6 +
        c₄ u * s ^ (4 : ℕ) / 24) (c₁ u + c₂ u * s + c₃ u * s ^ (2 : ℕ) / 2 + c₄ u * s ^ (3 : ℕ) / 6) s := by
      have := (((((hasDerivAt_id s).const_mul (c₁ u)).const_add (c u)).add
        (((hasDerivAt_pow 2 s).const_mul (c₂ u)).div_const 2)).add
        (((hasDerivAt_pow 3 s).const_mul (c₃ u)).div_const 6)).add
        (((hasDerivAt_pow 4 s).const_mul (c₄ u)).div_const 24)
      convert this using 1 <;> first | rfl | (simp; ring) | simp
    have := ((hc (u + s)).comp s ((hasDerivAt_id s).const_add u)).sub hp
    convert this using 1 <;> first | rfl | simp
  · intro s hs
    have := (h5 s hs).2.2.2
    calc _ ≤ S₅ * |s| ^ (4 : ℕ) / 24 := this
      _ = S₅ / 24 * |s| ^ (4 : ℕ) := by ring
  intro s hs
  have hs' : s ∈ Icc (-t) t := ⟨by linarith [hs.1], hs.2⟩
  have hs'' : -s ∈ Icc (-t) t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have habs : |s| = s := abs_of_nonneg hs.1
  have habs' : |-s| = s := by rw [abs_neg, habs]
  obtain ⟨p3, p2, p1, p0⟩ := h4 s hs'
  obtain ⟨m3, m2, m1, m0⟩ := h4 (-s) hs''
  obtain ⟨q3, q2, q1, q0⟩ := h5 s hs'
  obtain ⟨n3, n2, n1, n0⟩ := h5 (-s) hs''
  have r0 := h5c s hs'
  have r0' := h5c (-s) hs''
  rw [habs] at p3 p2 p1 p0 q3 q2 q1 q0 r0
  rw [habs'] at m3 m2 m1 m0 n3 n2 n1 n0 r0'
  have hu : u + -s = u - s := by ring
  rw [hu] at m3 m2 m1 m0 n3 n2 n1 n0 r0'
  have e_p0 := abs_le.mp p0
  have e_m0 := abs_le.mp m0
  have e_r0 := abs_le.mp r0
  have e_r0' := abs_le.mp r0'
  have e_p1 := abs_le.mp p1
  have e_m1 := abs_le.mp m1
  have e_q1 := abs_le.mp q1
  have e_n1 := abs_le.mp n1
  have e_p2 := abs_le.mp p2
  have e_m2 := abs_le.mp m2
  have e_q0 := abs_le.mp q0
  have e_n0 := abs_le.mp n0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold fjEven
    rw [abs_le]
    constructor <;> linarith only [e_p0.1, e_p0.2, e_m0.1, e_m0.2]
  · unfold fjOdd
    rw [abs_le]
    constructor <;> linarith only [e_r0.1, e_r0.2, e_r0'.1, e_r0'.2]
  · unfold fjOdd
    rw [abs_le]
    constructor <;> linarith only [e_p1.1, e_p1.2, e_m1.1, e_m1.2]
  · unfold fjEven
    rw [abs_le]
    constructor <;> linarith only [e_q0.1, e_q0.2, e_n0.1, e_n0.2]
  · unfold fjEven
    rw [abs_le]
    constructor <;> linarith only [e_p2.1, e_p2.2, e_m2.1, e_m2.2]
  · unfold fjOdd
    rw [abs_le]
    constructor <;> linarith only [e_q1.1, e_q1.2, e_n1.1, e_n1.2]

end

/-! ## Stage 3: the closed-form auxiliaries and their bounds -/

section

variable {c c₁ c₂ c₃ c₄ c₅ σ : ℝ → ℝ} {u t S₄ S₅ : ℝ}

/-- `N = o·tE − O(E + te)` (one quarter of the centre numerator `H`). -/
noncomputable def fjN (σ c : ℝ → ℝ) (u t : ℝ) : ℝ :=
  fjOdd c u t * t * fjE σ u t - fjO σ u t * (fjE σ u t + t * fjEven c u t)

/-- `M = o₁·tE − O(2e + te₁)` (one quarter of the time jet of `H`). -/
noncomputable def fjM (σ c c₁ : ℝ → ℝ) (u t : ℝ) : ℝ :=
  fjEven c₁ u t * t * fjE σ u t - fjO σ u t * (2 * fjEven c u t + t * fjOdd c₁ u t)

/-- `K₁ = t²o₁ − 5to + 8O`. -/
noncomputable def fjK₁ (σ c c₁ : ℝ → ℝ) (u t : ℝ) : ℝ :=
  t ^ (2 : ℕ) * fjEven c₁ u t - 5 * t * fjOdd c u t + 8 * fjO σ u t

/-- `K₂ = 3te − 3E − t²e₁`. -/
noncomputable def fjK₂ (σ c c₁ : ℝ → ℝ) (u t : ℝ) : ℝ :=
  3 * t * fjEven c u t - 3 * fjE σ u t - t ^ (2 : ℕ) * fjOdd c₁ u t

/-- `Λ = to − 2O`. -/
noncomputable def fjLam (σ c : ℝ → ℝ) (u t : ℝ) : ℝ := t * fjOdd c u t - 2 * fjO σ u t

/-- `Y = te − E`. -/
noncomputable def fjY (σ c : ℝ → ℝ) (u t : ℝ) : ℝ := t * fjEven c u t - fjE σ u t

theorem fj_excess_eq (σ c c₁ : ℝ → ℝ) (u t : ℝ) :
    t * fjM σ c c₁ u t - 5 * fjN σ c u t = fjE σ u t * fjK₁ σ c c₁ u t + fjO σ u t * fjK₂ σ c c₁ u t := by
  unfold fjM fjN fjK₁ fjK₂
  ring

theorem fjN_eq (σ c : ℝ → ℝ) (u t : ℝ) :
    fjN σ c u t = fjE σ u t * fjLam σ c u t - fjO σ u t * fjY σ c u t := by
  unfold fjN fjLam fjY
  ring

/-- The remainder functions. -/
noncomputable def fjWt (c c₁ c₃ : ℝ → ℝ) (u t : ℝ) : ℝ :=
  t * fjEven c₁ u t - fjOdd c u t - c₃ u * t ^ (3 : ℕ) / 3
noncomputable def fjOmega (c₂ c₃ : ℝ → ℝ) (u t : ℝ) : ℝ := fjOdd c₂ u t - c₃ u * t
noncomputable def fjP₀ (c₁ c₂ : ℝ → ℝ) (u t : ℝ) : ℝ := fjOdd c₁ u t - c₂ u * t
noncomputable def fjEta (c₂ : ℝ → ℝ) (u t : ℝ) : ℝ := fjEven c₂ u t - c₂ u

theorem hasDerivAt_fjWt (hc : ∀ x, HasDerivAt c (c₁ x) x) (hc₁ : ∀ x, HasDerivAt c₁ (c₂ x) x)
    (c₃ : ℝ → ℝ) (u t : ℝ) :
    HasDerivAt (fjWt c c₁ c₃ u) (t * fjOmega c₂ c₃ u t) t := by
  have h1 := (hasDerivAt_id t).mul (hasDerivAt_fjEven hc₁ u t)
  have h2 := hasDerivAt_fjOdd hc u t
  have h3 := ((hasDerivAt_pow 3 t).const_mul (c₃ u)).div_const 3
  have := (h1.sub h2).sub h3
  unfold fjWt fjOmega
  convert this using 1 <;> first | rfl | ((try simp only [id_eq]); push_cast; ring)

theorem hasDerivAt_fjK₁ (hσ : ∀ x, HasDerivAt σ (c x) x) (hc : ∀ x, HasDerivAt c (c₁ x) x)
    (hc₁ : ∀ x, HasDerivAt c₁ (c₂ x) x) (c₃ : ℝ → ℝ) (u t : ℝ) :
    HasDerivAt (fjK₁ σ c c₁ u) (t ^ (2 : ℕ) * fjOmega c₂ c₃ u t - 3 * fjWt c c₁ c₃ u t) t := by
  have h1 := (hasDerivAt_pow 2 t).mul (hasDerivAt_fjEven hc₁ u t)
  have h2 := ((hasDerivAt_id t).const_mul (5 : ℝ)).mul (hasDerivAt_fjOdd hc u t)
  have h3 := (hasDerivAt_fjO hσ u t).const_mul (8 : ℝ)
  have := (h1.sub h2).add h3
  unfold fjK₁ fjOmega fjWt
  convert this using 1 <;> first | rfl | ((try simp only [id_eq]); push_cast; ring)

theorem hasDerivAt_fjK₂ (hσ : ∀ x, HasDerivAt σ (c x) x) (hc : ∀ x, HasDerivAt c (c₁ x) x)
    (hc₁ : ∀ x, HasDerivAt c₁ (c₂ x) x) (u t : ℝ) :
    HasDerivAt (fjK₂ σ c c₁ u) (t * fjP₀ c₁ c₂ u t - t ^ (2 : ℕ) * fjEta c₂ u t) t := by
  have h1 := ((hasDerivAt_id t).const_mul (3 : ℝ)).mul (hasDerivAt_fjEven hc u t)
  have h2 := (hasDerivAt_fjE hσ u t).const_mul (3 : ℝ)
  have h3 := (hasDerivAt_pow 2 t).mul (hasDerivAt_fjOdd hc₁ u t)
  have := (h1.sub h2).sub h3
  unfold fjK₂ fjP₀ fjEta
  convert this using 1 <;> first | rfl | ((try simp only [id_eq]); push_cast; ring)

theorem hasDerivAt_fjLam_sub (hσ : ∀ x, HasDerivAt σ (c x) x) (hc : ∀ x, HasDerivAt c (c₁ x) x)
    (c₃ : ℝ → ℝ) (u t : ℝ) :
    HasDerivAt (fun t => fjLam σ c u t - c₃ u * t ^ (4 : ℕ) / 12) (fjWt c c₁ c₃ u t) t := by
  have h1 := (hasDerivAt_id t).mul (hasDerivAt_fjOdd hc u t)
  have h2 := (hasDerivAt_fjO hσ u t).const_mul (2 : ℝ)
  have h3 := ((hasDerivAt_pow 4 t).const_mul (c₃ u)).div_const 12
  have := (h1.sub h2).sub h3
  unfold fjLam fjWt
  convert this using 1 <;> first | rfl | ((try simp only [id_eq]); push_cast; ring)

theorem hasDerivAt_fjY_sub (hσ : ∀ x, HasDerivAt σ (c x) x) (hc : ∀ x, HasDerivAt c (c₁ x) x)
    (c₂ : ℝ → ℝ) (u t : ℝ) :
    HasDerivAt (fun t => fjY σ c u t - c₂ u * t ^ (3 : ℕ) / 3) (t * fjP₀ c₁ c₂ u t) t := by
  have h1 := (hasDerivAt_id t).mul (hasDerivAt_fjEven hc u t)
  have h2 := hasDerivAt_fjE hσ u t
  have h3 := ((hasDerivAt_pow 3 t).const_mul (c₂ u)).div_const 3
  have := (h1.sub h2).sub h3
  unfold fjY fjP₀
  convert this using 1 <;> first | rfl | ((try simp only [id_eq]); push_cast; ring)

theorem hasDerivAt_fjE_sub (hσ : ∀ x, HasDerivAt σ (c x) x) (c₂ : ℝ → ℝ) (u t : ℝ) :
    HasDerivAt (fun t => fjE σ u t - c u * t - c₂ u * t ^ (3 : ℕ) / 6)
      (fjEven c u t - (c u + c₂ u * t ^ (2 : ℕ) / 2)) t := by
  have h1 := hasDerivAt_fjE hσ u t
  have h2 := (hasDerivAt_id t).const_mul (c u)
  have h3 := ((hasDerivAt_pow 3 t).const_mul (c₂ u)).div_const 6
  have := (h1.sub h2).sub h3
  convert this using 1 <;> first | rfl | ((try simp only [id_eq]); push_cast; ring)

theorem hasDerivAt_fjO_sub (hσ : ∀ x, HasDerivAt σ (c x) x) (c₁ c₃ : ℝ → ℝ) (u t : ℝ) :
    HasDerivAt (fun t => fjO σ u t - c₁ u * t ^ (2 : ℕ) / 2 - c₃ u * t ^ (4 : ℕ) / 24)
      (fjOdd c u t - (c₁ u * t + c₃ u * t ^ (3 : ℕ) / 6)) t := by
  have h1 := hasDerivAt_fjO hσ u t
  have h2 := ((hasDerivAt_pow 2 t).const_mul (c₁ u)).div_const 2
  have h3 := ((hasDerivAt_pow 4 t).const_mul (c₃ u)).div_const 24
  have := (h1.sub h2).sub h3
  convert this using 1 <;> first | rfl | ((try simp only [id_eq]); push_cast; ring)

/-- **Component bounds of the frozen-jet growth estimate.** -/
theorem fj_component_bounds (ht : 0 ≤ t)
    (hσ : ∀ x, HasDerivAt σ (c x) x)
    (hc : ∀ x, HasDerivAt c (c₁ x) x) (hc₁ : ∀ x, HasDerivAt c₁ (c₂ x) x)
    (hc₂ : ∀ x, HasDerivAt c₂ (c₃ x) x) (hc₃ : ∀ x, HasDerivAt c₃ (c₄ x) x)
    (hc₄ : ∀ x, HasDerivAt c₄ (c₅ x) x)
    (hS₄ : ∀ x ∈ Icc (u - t) (u + t), |c₄ x| ≤ S₄) (hS₅ : ∀ x ∈ Icc (u - t) (u + t), |c₅ x| ≤ S₅) :
    |fjK₁ σ c c₁ u t| ≤ 2 / 45 * S₅ * t ^ (6 : ℕ) ∧
    |fjK₂ σ c c₁ u t| ≤ 2 / 15 * S₄ * t ^ (5 : ℕ) ∧
    |fjLam σ c u t - c₃ u * t ^ (4 : ℕ) / 12| ≤ S₅ * t ^ (6 : ℕ) / 180 ∧
    |fjY σ c u t - c₂ u * t ^ (3 : ℕ) / 3| ≤ S₄ * t ^ (5 : ℕ) / 30 ∧
    |fjE σ u t - c u * t - c₂ u * t ^ (3 : ℕ) / 6| ≤ S₄ * t ^ (5 : ℕ) / 120 ∧
    |fjO σ u t - c₁ u * t ^ (2 : ℕ) / 2 - c₃ u * t ^ (4 : ℕ) / 24| ≤ S₅ * t ^ (6 : ℕ) / 720 := by
  have hpt := fj_pointwise_bounds ht hc hc₁ hc₂ hc₃ hc₄ hS₄ hS₅
  have hS₄0 : 0 ≤ S₄ := le_trans (abs_nonneg _) (hS₄ u ⟨by linarith, by linarith⟩)
  have hS₅0 : 0 ≤ S₅ := le_trans (abs_nonneg _) (hS₅ u ⟨by linarith, by linarith⟩)
  -- `|W̃ s| ≤ S₅ s⁵ / 30`
  have hWt : ∀ s ∈ Icc (0 : ℝ) t, |fjWt c c₁ c₃ u s| ≤ S₅ / 6 * s ^ (4 + 1) / (4 + 1) := by
    refine abs_le_pow_div_of_abs_deriv_le ht ?_ (fun s _ => hasDerivAt_fjWt hc hc₁ c₃ u s) ?_
    · simp [fjWt, fjOdd_zero]
    · intro s hs
      have hω := (hpt s hs).2.2.2.2.2
      rw [abs_mul, abs_of_nonneg hs.1]
      unfold fjOmega
      calc s * |fjOdd c₂ u s - c₃ u * s| ≤ s * (S₅ * s ^ (3 : ℕ) / 6) :=
            mul_le_mul_of_nonneg_left hω hs.1
        _ = S₅ / 6 * s ^ (4 : ℕ) := by ring
  -- `|K₁| ≤ (2/45) S₅ t⁶`
  have hK₁ : ∀ s ∈ Icc (0 : ℝ) t, |fjK₁ σ c c₁ u s| ≤ 4 * S₅ / 15 * s ^ (5 + 1) / (5 + 1) := by
    refine abs_le_pow_div_of_abs_deriv_le ht ?_ (fun s _ => hasDerivAt_fjK₁ hσ hc hc₁ c₃ u s) ?_
    · simp [fjK₁, fjOdd_zero, fjO_zero]
    · intro s hs
      have hω := (hpt s hs).2.2.2.2.2
      have hW := hWt s hs
      have hs0 := hs.1
      calc |s ^ (2 : ℕ) * fjOmega c₂ c₃ u s - 3 * fjWt c c₁ c₃ u s|
          ≤ |s ^ (2 : ℕ) * fjOmega c₂ c₃ u s| + |3 * fjWt c c₁ c₃ u s| := abs_sub _ _
        _ = s ^ (2 : ℕ) * |fjOdd c₂ u s - c₃ u * s| + 3 * |fjWt c c₁ c₃ u s| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ (2 : ℕ))]
            norm_num [fjOmega]
        _ ≤ s ^ (2 : ℕ) * (S₅ * s ^ (3 : ℕ) / 6) + 3 * (S₅ / 6 * s ^ (4 + 1) / (4 + 1)) := by
            gcongr
        _ = 4 * S₅ / 15 * s ^ (5 : ℕ) := by ring
  -- `|K₂| ≤ (2/15) S₄ t⁵`
  have hK₂ : ∀ s ∈ Icc (0 : ℝ) t, |fjK₂ σ c c₁ u s| ≤ 2 * S₄ / 3 * s ^ (4 + 1) / (4 + 1) := by
    refine abs_le_pow_div_of_abs_deriv_le ht ?_ (fun s _ => hasDerivAt_fjK₂ hσ hc hc₁ u s) ?_
    · simp [fjK₂, fjE_zero, fjOdd_zero]
    · intro s hs
      have hP := (hpt s hs).2.2.1
      have hη := (hpt s hs).2.2.2.2.1
      have hs0 := hs.1
      calc |s * fjP₀ c₁ c₂ u s - s ^ (2 : ℕ) * fjEta c₂ u s|
          ≤ |s * fjP₀ c₁ c₂ u s| + |s ^ (2 : ℕ) * fjEta c₂ u s| := abs_sub _ _
        _ = s * |fjOdd c₁ u s - c₂ u * s| + s ^ (2 : ℕ) * |fjEven c₂ u s - c₂ u| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ (2 : ℕ))]
            rfl
        _ ≤ s * (S₄ * s ^ (3 : ℕ) / 6) + s ^ (2 : ℕ) * (S₄ * s ^ (2 : ℕ) / 2) := by gcongr
        _ = 2 * S₄ / 3 * s ^ (4 : ℕ) := by ring
  -- `|Λ − c₃t⁴/12| ≤ S₅ t⁶/180`
  have hΛ : ∀ s ∈ Icc (0 : ℝ) t,
      |fjLam σ c u s - c₃ u * s ^ (4 : ℕ) / 12| ≤ S₅ / 30 * s ^ (5 + 1) / (5 + 1) := by
    refine abs_le_pow_div_of_abs_deriv_le ht ?_ (fun s _ => hasDerivAt_fjLam_sub hσ hc c₃ u s) ?_
    · simp [fjLam, fjOdd_zero, fjO_zero]
    · intro s hs
      have := hWt s hs
      calc |fjWt c c₁ c₃ u s| ≤ S₅ / 6 * s ^ (4 + 1) / (4 + 1) := this
        _ = S₅ / 30 * s ^ (5 : ℕ) := by ring
  -- `|Y − c₂t³/3| ≤ S₄ t⁵/30`
  have hY : ∀ s ∈ Icc (0 : ℝ) t,
      |fjY σ c u s - c₂ u * s ^ (3 : ℕ) / 3| ≤ S₄ / 6 * s ^ (4 + 1) / (4 + 1) := by
    refine abs_le_pow_div_of_abs_deriv_le ht ?_ (fun s _ => hasDerivAt_fjY_sub hσ hc c₂ u s) ?_
    · simp [fjY, fjE_zero]
    · intro s hs
      have hP := (hpt s hs).2.2.1
      rw [abs_mul, abs_of_nonneg hs.1]
      unfold fjP₀
      calc s * |fjOdd c₁ u s - c₂ u * s| ≤ s * (S₄ * s ^ (3 : ℕ) / 6) :=
            mul_le_mul_of_nonneg_left hP hs.1
        _ = S₄ / 6 * s ^ (4 : ℕ) := by ring
  -- `|E − c₀t − c₂t³/6| ≤ S₄ t⁵/120`
  have hE : ∀ s ∈ Icc (0 : ℝ) t,
      |fjE σ u s - c u * s - c₂ u * s ^ (3 : ℕ) / 6| ≤ S₄ / 24 * s ^ (4 + 1) / (4 + 1) := by
    refine abs_le_pow_div_of_abs_deriv_le ht ?_ (fun s _ => hasDerivAt_fjE_sub hσ c₂ u s) ?_
    · simp [fjE_zero]
    · intro s hs
      have := (hpt s hs).1
      calc _ ≤ S₄ * s ^ (4 : ℕ) / 24 := this
        _ = S₄ / 24 * s ^ (4 : ℕ) := by ring
  -- `|O − c₁t²/2 − c₃t⁴/24| ≤ S₅ t⁶/720`
  have hO : ∀ s ∈ Icc (0 : ℝ) t,
      |fjO σ u s - c₁ u * s ^ (2 : ℕ) / 2 - c₃ u * s ^ (4 : ℕ) / 24| ≤ S₅ / 120 * s ^ (5 + 1) / (5 + 1) := by
    refine abs_le_pow_div_of_abs_deriv_le ht ?_ (fun s _ => hasDerivAt_fjO_sub hσ c₁ c₃ u s) ?_
    · simp [fjO_zero]
    · intro s hs
      have := (hpt s hs).2.1
      calc _ ≤ S₅ * s ^ (5 : ℕ) / 120 := this
        _ = S₅ / 120 * s ^ (5 : ℕ) := by ring
  have htt : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hK₁ t htt
    calc _ ≤ 4 * S₅ / 15 * t ^ (5 + 1) / (5 + 1) := this
      _ = 2 / 45 * S₅ * t ^ (6 : ℕ) := by ring
  · have := hK₂ t htt
    calc _ ≤ 2 * S₄ / 3 * t ^ (4 + 1) / (4 + 1) := this
      _ = 2 / 15 * S₄ * t ^ (5 : ℕ) := by ring
  · have := hΛ t htt
    calc _ ≤ S₅ / 30 * t ^ (5 + 1) / (5 + 1) := this
      _ = S₅ * t ^ (6 : ℕ) / 180 := by ring
  · have := hY t htt
    calc _ ≤ S₄ / 6 * t ^ (4 + 1) / (4 + 1) := this
      _ = S₄ * t ^ (5 : ℕ) / 30 := by ring
  · have := hE t htt
    calc _ ≤ S₄ / 24 * t ^ (4 + 1) / (4 + 1) := this
      _ = S₄ * t ^ (5 : ℕ) / 120 := by ring
  · have := hO t htt
    calc _ ≤ S₅ / 120 * t ^ (5 + 1) / (5 + 1) := this
      _ = S₅ * t ^ (6 : ℕ) / 720 := by ring

end

end RHTower
