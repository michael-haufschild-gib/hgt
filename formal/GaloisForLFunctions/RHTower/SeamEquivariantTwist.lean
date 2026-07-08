/-
Symmetric nonvanishing loops classify by winding and fixed-angle sign.

A loop `γ : ℝ → ℂ` is equivariant for the angle involution `θ ↦ π − θ` (fixed point `π/2`) when
`γ (π − θ) = conj (γ θ)`; this realises the critical-line reflection on a line-centred circle, and
forces the fixed-angle value `γ (π/2)` to be real.  For any continuous logarithm `L` of such a loop
(`exp ∘ L = γ`) the twist of `L` under the reflection pullback — the difference
`conj (L (π − θ)) − L θ` — is a *constant* integer multiple of `2πi`: its exponential is `1`, so the
integer is locally constant on the connected line (`equivariant_log_twist`).  At the fixed angle the
same relation pins the imaginary part `(L (π/2)).im = π·k`, so `γ (π/2)` is real with sign `(−1)^k`:
the parity of the twist integer *is* the fixed-angle sign (`twist_parity_eq_sign`).

Two equivariant loops with equal winding and equal fixed-angle sign are joined by an equivariant
homotopy: shifting one logarithm by `2πi·m` (with `2m = k₀ − k₁`, available because the signs, hence
the parities, agree) makes both twists equal, and the twist-preserving linear interpolation of the
logarithms is a homotopy through nonvanishing loops respecting the reflection
(`equivariant_joined_of_winding_sign_eq`).  Winding and fixed-angle sign are the *complete* pair of
invariants (`equivariant_joined_iff`): the two conserved quantities are the winding number
(deformation-invariant) and the fixed-angle real sign (transported by the intermediate value theorem
along the nonvanishing real family), so `π₀` of the equivariant loop space is `ℤ × ℤ/2`.
-/
import GaloisForLFunctions.RHTower.ConnectedSymmetryBarrier

open Complex Set

namespace RHTower

/-! ### §1 The reflection twist of a continuous logarithm is a constant integer -/

/-- **The reflection twist is a constant integer.**  For an equivariant nonvanishing loop `γ`
(`γ (π − θ) = conj (γ θ)`) and any continuous logarithm `L` (`exp (L t) = γ t`), the reflected
conjugate log `conj (L (π − θ))` differs from `L θ` by a fixed integer multiple of `2πi`.  The
reflected conjugate log `M θ := conj (L (π − θ))` satisfies `exp (M θ) = γ θ = exp (L θ)`, so the
difference `L θ − M θ` is a continuous `2πiℤ`-valued function on the connected line, hence constant;
the constant is `2πi·k` for a single integer `k`. -/
theorem equivariant_log_twist {γ : ℝ → ℂ}
    (heq : ∀ θ : ℝ, γ (Real.pi - θ) = (starRingEnd ℂ) (γ θ))
    {L : ℝ → ℂ} (hLc : Continuous L) (hLe : ∀ t, exp (L t) = γ t) :
    ∃ k : ℤ, ∀ θ : ℝ,
      (starRingEnd ℂ) (L (Real.pi - θ)) = L θ - (k : ℂ) * (2 * (Real.pi : ℂ) * I) := by
  have hMexp : ∀ θ, exp ((starRingEnd ℂ) (L (Real.pi - θ))) = γ θ := by
    intro θ
    rw [Complex.exp_conj, hLe (Real.pi - θ), heq θ, Complex.conj_conj]
  have hEq : ∀ θ, exp (L θ) = exp ((starRingEnd ℂ) (L (Real.pi - θ))) :=
    fun θ => by rw [hLe θ, hMexp θ]
  set d : ℝ → ℂ := fun θ => L θ - (starRingEnd ℂ) (L (Real.pi - θ)) with hd
  have hMc : Continuous (fun θ => (starRingEnd ℂ) (L (Real.pi - θ))) :=
    Complex.continuous_conj.comp (hLc.comp (continuous_const.sub continuous_id))
  have hdc : Continuous d := hLc.sub hMc
  have hmem : ∀ θ, ∃ n : ℤ, d θ = (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    intro θ
    have h1 : exp (d θ) = 1 := by
      rw [hd]; simp only; rw [Complex.exp_sub, hEq θ]; exact div_self (Complex.exp_ne_zero _)
    exact (Complex.exp_eq_one_iff).mp h1
  choose n hn using hmem
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have hncont : Continuous n := by
    rw [Complex.isClosedEmbedding_intCast.isEmbedding.continuous_iff]
    have hcomp : (Int.cast ∘ n : ℝ → ℂ) = fun θ => d θ / (2 * (Real.pi : ℂ) * I) := by
      funext θ; simp only [Function.comp_apply]; rw [hn θ]; field_simp
    rw [hcomp]; exact hdc.div_const _
  have hlc : IsLocallyConstant n := (IsLocallyConstant.iff_continuous n).mpr hncont
  refine ⟨n 0, fun θ => ?_⟩
  have hn0 : n θ = n 0 :=
    hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ θ) (mem_univ 0)
  have hdθ : d θ = (n 0 : ℂ) * (2 * (Real.pi : ℂ) * I) := by rw [hn θ, hn0]
  rw [hd] at hdθ; simp only at hdθ
  linear_combination -hdθ

/-! ### §2 The fixed-angle value: reality and the sign = twist parity -/

/-- **Reality at the fixed angle.**  An equivariant loop is real at the involution's fixed point
`π/2`: `γ (π/2) = γ (π − π/2) = conj (γ (π/2))`, so `γ (π/2)` equals its own conjugate. -/
theorem equivariant_midpoint_im_zero {γ : ℝ → ℂ}
    (heq : ∀ θ : ℝ, γ (Real.pi - θ) = (starRingEnd ℂ) (γ θ)) :
    (γ (Real.pi / 2)).im = 0 := by
  have h := heq (Real.pi / 2)
  rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- **The fixed-angle sign is the twist parity.**  With `L` a continuous logarithm of `γ` and twist
integer `k`, the fixed-point relation `conj (L (π/2)) = L (π/2) − 2πi·k` forces `(L (π/2)).im = π·k`;
hence `γ (π/2) = exp (L (π/2)) = exp (Re L (π/2)) · (−1)^k` is a positive real times `(−1)^k`, so its
real part is positive exactly when `k` is even. -/
theorem twist_parity_eq_sign {γ : ℝ → ℂ} {L : ℝ → ℂ} {k : ℤ}
    (hLe : ∀ t, exp (L t) = γ t)
    (htw : ∀ θ : ℝ,
      (starRingEnd ℂ) (L (Real.pi - θ)) = L θ - (k : ℂ) * (2 * (Real.pi : ℂ) * I)) :
    (0 < (γ (Real.pi / 2)).re ↔ Even k) := by
  set w := L (Real.pi / 2) with hwdef
  have hfix : (starRingEnd ℂ) w = w - (k : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    have h := htw (Real.pi / 2)
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, ← hwdef] at h
    exact h
  have him : w.im = Real.pi * k := by
    have h2 := congrArg Complex.im hfix
    simp only [Complex.conj_im, Complex.sub_im, Complex.mul_im, Complex.mul_re,
      Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat] at h2
    ring_nf at h2 ⊢
    linarith
  have hγw : γ (Real.pi / 2) = exp w := (hLe (Real.pi / 2)).symm
  have hexpw : exp w = ↑(Real.exp w.re) * (-1 : ℂ) ^ k := by
    conv_lhs => rw [← Complex.re_add_im w]
    rw [him, Complex.exp_add, Complex.ofReal_exp]
    congr 1
    have hcast : ((↑(Real.pi * (k : ℝ)) : ℂ)) * I = (k : ℂ) * ((↑Real.pi : ℂ) * I) := by
      push_cast; ring
    rw [hcast, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [hγw, hexpw]
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, mul_one, Complex.ofReal_re]
    exact iff_of_true (Real.exp_pos _) hk
  · rw [hk.neg_one_zpow, mul_neg_one, Complex.neg_re, Complex.ofReal_re]
    refine iff_of_false (fun h => ?_) (Int.not_even_iff_odd.mpr hk)
    linarith [Real.exp_pos w.re]

/-! ### §3 The h-principle: equal winding and sign give an equivariant homotopy -/

/-- **Sufficiency of winding and fixed-angle sign.**  Two equivariant nonvanishing loops on
`[0, 2π]` with equal winding number and equal fixed-angle real sign are joined by a homotopy through
nonvanishing loops respecting the reflection.  Equal signs give equal twist parities
(`twist_parity_eq_sign`), so `2m = k₀ − k₁` for some integer `m`; shifting the second logarithm by
`2πi·m` raises its twist to `k₀` without changing its exponential, and the twist-preserving linear
interpolation `L_σ = (1 − σ) L₀ + σ L₁'` gives `H σ θ := exp (L_σ θ)`.  This never vanishes, closes
up (equal increment `2πi·w` at both ends), interpolates the two loops, and its conjugate under the
reflection differs from its reflected value by `exp (−2πi·k₀) = 1`. -/
theorem equivariant_joined_of_winding_sign_eq {γ₀ γ₁ : ℝ → ℂ}
    (h₀ : IsLoop γ₀ 0 (2 * Real.pi)) (h₁ : IsLoop γ₁ 0 (2 * Real.pi))
    (heq₀ : ∀ θ : ℝ, γ₀ (Real.pi - θ) = (starRingEnd ℂ) (γ₀ θ))
    (heq₁ : ∀ θ : ℝ, γ₁ (Real.pi - θ) = (starRingEnd ℂ) (γ₁ θ))
    (hw : windingNumber γ₀ 0 (2 * Real.pi) = windingNumber γ₁ 0 (2 * Real.pi))
    (hsign : (0 < (γ₀ (Real.pi / 2)).re ↔ 0 < (γ₁ (Real.pi / 2)).re)) :
    ∃ H : ℝ → ℝ → ℂ,
      Continuous (fun p : ℝ × ℝ => H p.1 p.2) ∧
      (∀ σ t, H σ t ≠ 0) ∧
      (∀ σ, H σ 0 = H σ (2 * Real.pi)) ∧
      (∀ t, H 0 t = γ₀ t) ∧
      (∀ t, H 1 t = γ₁ t) ∧
      (∀ σ θ, H σ (Real.pi - θ) = (starRingEnd ℂ) (H σ θ)) := by
  obtain ⟨hL₀c, hL₀e⟩ := contLog_spec h₀.continuous h₀.nonzero
  obtain ⟨hL₁c, hL₁e⟩ := contLog_spec h₁.continuous h₁.nonzero
  obtain ⟨k₀, htw₀⟩ := equivariant_log_twist heq₀ hL₀c hL₀e
  obtain ⟨k₁, htw₁⟩ := equivariant_log_twist heq₁ hL₁c hL₁e
  have hs₀ := twist_parity_eq_sign hL₀e htw₀
  have hs₁ := twist_parity_eq_sign hL₁e htw₁
  have hpar : Even k₀ ↔ Even k₁ := hs₀.symm.trans (hsign.trans hs₁)
  obtain ⟨m, hm⟩ := Int.even_sub.mpr hpar
  set L₁' : ℝ → ℂ := fun θ => contLog γ₁ θ + (m : ℂ) * (2 * (Real.pi : ℂ) * I) with hL₁'def
  have hL₁'c : Continuous L₁' := by rw [hL₁'def]; exact hL₁c.add continuous_const
  have hL₁'e : ∀ t, exp (L₁' t) = γ₁ t := by
    intro t
    simp only [hL₁'def]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    exact hL₁e t
  have htw₁' : ∀ θ : ℝ,
      (starRingEnd ℂ) (L₁' (Real.pi - θ)) = L₁' θ - (k₀ : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    intro θ
    have hk : (k₀ : ℂ) = (k₁ : ℂ) + 2 * (m : ℂ) := by
      have hz : k₀ = k₁ + 2 * m := by omega
      exact_mod_cast hz
    have hconjm : (starRingEnd ℂ) ((m : ℂ) * (2 * (Real.pi : ℂ) * I))
        = -((m : ℂ) * (2 * (Real.pi : ℂ) * I)) := by
      simp only [map_mul, Complex.conj_I, map_intCast, Complex.conj_ofReal, map_ofNat]
      ring
    simp only [hL₁'def]
    rw [map_add, htw₁ θ, hconjm, hk]
    ring
  have hinc₀ := contLog_increment h₀ hL₀c hL₀e
  have hinc₁ := contLog_increment h₁ hL₁'c hL₁'e
  refine ⟨fun σ θ => exp ((1 - (σ : ℂ)) * contLog γ₀ θ + (σ : ℂ) * L₁' θ),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.continuous_exp.comp
      (((continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst)).mul
        (hL₀c.comp continuous_snd)).add
        ((Complex.continuous_ofReal.comp continuous_fst).mul (hL₁'c.comp continuous_snd)))
  · intro σ θ; exact Complex.exp_ne_zero _
  · intro σ
    show exp ((1 - (σ : ℂ)) * contLog γ₀ 0 + (σ : ℂ) * L₁' 0) =
      exp ((1 - (σ : ℂ)) * contLog γ₀ (2 * Real.pi) + (σ : ℂ) * L₁' (2 * Real.pi))
    have hb₀ : contLog γ₀ (2 * Real.pi) =
        contLog γ₀ 0 + ↑(windingNumber γ₀ 0 (2 * Real.pi)) * (2 * (Real.pi : ℂ) * I) := by
      linear_combination hinc₀
    have hb₁ : L₁' (2 * Real.pi) =
        L₁' 0 + ↑(windingNumber γ₀ 0 (2 * Real.pi)) * (2 * (Real.pi : ℂ) * I) := by
      rw [hw]; linear_combination hinc₁
    rw [hb₀, hb₁,
      show (1 - (σ : ℂ)) * (contLog γ₀ 0 +
            ↑(windingNumber γ₀ 0 (2 * Real.pi)) * (2 * (Real.pi : ℂ) * I)) +
          (σ : ℂ) * (L₁' 0 + ↑(windingNumber γ₀ 0 (2 * Real.pi)) * (2 * (Real.pi : ℂ) * I)) =
          ((1 - (σ : ℂ)) * contLog γ₀ 0 + (σ : ℂ) * L₁' 0) +
            ↑(windingNumber γ₀ 0 (2 * Real.pi)) * (2 * (Real.pi : ℂ) * I) from by ring]
    conv_rhs => rw [Complex.exp_add]
    rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · intro θ
    show exp ((1 - ((0 : ℝ) : ℂ)) * contLog γ₀ θ + ((0 : ℝ) : ℂ) * L₁' θ) = γ₀ θ
    rw [Complex.ofReal_zero, sub_zero, one_mul, zero_mul, add_zero]
    exact hL₀e θ
  · intro θ
    show exp ((1 - ((1 : ℝ) : ℂ)) * contLog γ₀ θ + ((1 : ℝ) : ℂ) * L₁' θ) = γ₁ θ
    rw [Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add]
    exact hL₁'e θ
  · intro σ θ
    show exp ((1 - (σ : ℂ)) * contLog γ₀ (Real.pi - θ) + (σ : ℂ) * L₁' (Real.pi - θ)) =
      (starRingEnd ℂ) (exp ((1 - (σ : ℂ)) * contLog γ₀ θ + (σ : ℂ) * L₁' θ))
    have hc₀ : (starRingEnd ℂ) (contLog γ₀ θ)
        = contLog γ₀ (Real.pi - θ) - (k₀ : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      have h := htw₀ (Real.pi - θ)
      rwa [show Real.pi - (Real.pi - θ) = θ by ring] at h
    have hc₁ : (starRingEnd ℂ) (L₁' θ)
        = L₁' (Real.pi - θ) - (k₀ : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      have h := htw₁' (Real.pi - θ)
      rwa [show Real.pi - (Real.pi - θ) = θ by ring] at h
    rw [← Complex.exp_conj]
    have hconjB : (starRingEnd ℂ) ((1 - (σ : ℂ)) * contLog γ₀ θ + (σ : ℂ) * L₁' θ)
        = ((1 - (σ : ℂ)) * contLog γ₀ (Real.pi - θ) + (σ : ℂ) * L₁' (Real.pi - θ))
          - (k₀ : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      rw [map_add, map_mul, map_mul,
        show (starRingEnd ℂ) (1 - (σ : ℂ)) = 1 - (σ : ℂ) by
          rw [map_sub, map_one, Complex.conj_ofReal],
        Complex.conj_ofReal, hc₀, hc₁]
      ring
    rw [hconjB, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-! ### §4 Completeness: winding and fixed-angle sign are `π₀` of the equivariant loop space -/

/-- **Fixed-angle sign is conserved along an equivariant homotopy.**  Each member of a jointly
continuous nonvanishing family respecting the reflection is real at `π/2`, and the real family
`σ ↦ (H σ (π/2)).re` is continuous and never zero, so its sign cannot change: the sign at `σ = 0`
equals the sign at `σ = 1` by the intermediate value theorem. -/
theorem equivariant_midpoint_sign_conserved {H : ℝ → ℝ → ℂ}
    (hc : Continuous (fun p : ℝ × ℝ => H p.1 p.2))
    (hnv : ∀ σ t, H σ t ≠ 0)
    (hHeq : ∀ σ θ, H σ (Real.pi - θ) = (starRingEnd ℂ) (H σ θ)) :
    (0 < (H 0 (Real.pi / 2)).re ↔ 0 < (H 1 (Real.pi / 2)).re) := by
  have hcpt : Continuous (fun σ : ℝ => H σ (Real.pi / 2)) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have hreal : ∀ σ : ℝ, (H σ (Real.pi / 2)).im = 0 := by
    intro σ
    have h := hHeq σ (Real.pi / 2)
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at h
    exact Complex.conj_eq_iff_im.mp h.symm
  have hnv' : ∀ σ : ℝ, H σ (Real.pi / 2) ≠ 0 := fun σ => hnv σ (Real.pi / 2)
  have hgc : Continuous (fun σ : ℝ => (H σ (Real.pi / 2)).re) := Complex.continuous_re.comp hcpt
  have hgne : ∀ σ : ℝ, (H σ (Real.pi / 2)).re ≠ 0 := by
    intro σ hgt
    exact hnv' σ (Complex.ext hgt (hreal σ))
  have hcon : ContinuousOn (fun σ : ℝ => (H σ (Real.pi / 2)).re) (Set.Icc 0 1) := hgc.continuousOn
  constructor
  · intro h0
    by_contra h1
    have h1' : (H 1 (Real.pi / 2)).re < 0 := lt_of_le_of_ne (not_lt.mp h1) (hgne 1)
    have hmem : (0 : ℝ) ∈ Set.Icc ((H 1 (Real.pi / 2)).re) ((H 0 (Real.pi / 2)).re) :=
      ⟨h1'.le, h0.le⟩
    obtain ⟨c, _, hc0⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcon hmem
    exact hgne c hc0
  · intro h1
    by_contra h0
    have h0' : (H 0 (Real.pi / 2)).re < 0 := lt_of_le_of_ne (not_lt.mp h0) (hgne 0)
    have hmem : (0 : ℝ) ∈ Set.Icc ((H 0 (Real.pi / 2)).re) ((H 1 (Real.pi / 2)).re) :=
      ⟨h0'.le, h1.le⟩
    obtain ⟨c, _, hc0⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcon hmem
    exact hgne c hc0

/-- **The equivariant classification.**  Two equivariant nonvanishing loops on `[0, 2π]` are joined
by a homotopy through nonvanishing loops respecting the reflection **iff** they share both winding
number and fixed-angle real sign.  Sufficiency is `equivariant_joined_of_winding_sign_eq`; necessity
is that winding is a deformation invariant (`windingNumber_of_homotopic`) and the fixed-angle sign is
transported by the intermediate value theorem (`equivariant_midpoint_sign_conserved`).  Thus the two
invariants are complete: `π₀` of the equivariant nonvanishing loop space is `ℤ × ℤ/2`. -/
theorem equivariant_joined_iff {γ₀ γ₁ : ℝ → ℂ}
    (h₀ : IsLoop γ₀ 0 (2 * Real.pi)) (h₁ : IsLoop γ₁ 0 (2 * Real.pi))
    (heq₀ : ∀ θ : ℝ, γ₀ (Real.pi - θ) = (starRingEnd ℂ) (γ₀ θ))
    (heq₁ : ∀ θ : ℝ, γ₁ (Real.pi - θ) = (starRingEnd ℂ) (γ₁ θ)) :
    (windingNumber γ₀ 0 (2 * Real.pi) = windingNumber γ₁ 0 (2 * Real.pi) ∧
        (0 < (γ₀ (Real.pi / 2)).re ↔ 0 < (γ₁ (Real.pi / 2)).re)) ↔
      ∃ H : ℝ → ℝ → ℂ,
        Continuous (fun p : ℝ × ℝ => H p.1 p.2) ∧
        (∀ σ t, H σ t ≠ 0) ∧
        (∀ σ, H σ 0 = H σ (2 * Real.pi)) ∧
        (∀ t, H 0 t = γ₀ t) ∧
        (∀ t, H 1 t = γ₁ t) ∧
        (∀ σ θ, H σ (Real.pi - θ) = (starRingEnd ℂ) (H σ θ)) := by
  constructor
  · rintro ⟨hw, hsign⟩
    exact equivariant_joined_of_winding_sign_eq h₀ h₁ heq₀ heq₁ hw hsign
  · rintro ⟨H, hHc, hHnv, hHloop, hH0, hH1, hHeq⟩
    refine ⟨windingNumber_of_homotopic H hHc hHnv hHloop hH0 hH1, ?_⟩
    have hsc := equivariant_midpoint_sign_conserved hHc hHnv hHeq
    rw [hH0 (Real.pi / 2), hH1 (Real.pi / 2)] at hsc
    exact hsc

end RHTower
