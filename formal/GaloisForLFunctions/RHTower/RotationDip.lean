/-
Doc 51 §§2–3, 9 fusion (task #161): the rotation first-wrap dip.

At lattice order the walk's prefix sums have an EXACT closed form
  Σ_{m<M} cos(β + mθ) = r·cos γ − r·cos(γ + Mθ),
where r·e^{iγ} is the polar form of e^{iβ}/(1 − e^{iθ}) — the circle of doc
51 §2. The orbit angle γ + Mθ provably enters the up-window [−θ/2, θ/2]
(mod 2π) within one wrap, so cos(γ + Mθ) ≥ cos(θ/2) there, and a MISALIGNED
start (cos γ ≤ 1 − δ) takes a prefix dip

  S_M ≤ −r·(δ − (1 − cos(θ/2))).

This fuses (DRIFT-dip) and (HOLD-phase) at lattice order: the alignment
window IS the escape, everything outside it dips within one wrap. The
kill-power fades exactly at anti-phase θ ≈ π (cos(θ/2) → 0) — the marginal
dominance of doc 49 §2(1), as the physics demands: there the marginal term,
not the tail, does the killing.

`birthKilled_of_rotation` + `midCentralInput_of_rotation` descend the
`dip_kills` field of `MidCentral` to: "the future pushes are a rotation walk
and the birth is misaligned with depth below the dip".
-/
import GaloisForLFunctions.RHTower.MidCentral

namespace RHTower

open Finset

/-- pushSum is list sum. -/
theorem pushSum_eq_sum : ∀ l : List ℝ, pushSum l = l.sum := by
  intro l
  induction l with
  | nil => simp [pushSum]
  | cons q qs ih => simp [pushSum, ih]

/-- Range-map list sums are Finset range sums. -/
theorem sum_map_range (g : ℕ → ℝ) : ∀ M : ℕ,
    ((List.range M).map g).sum = ∑ m ∈ Finset.range M, g m := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.range_succ, List.map_append, List.sum_append,
      Finset.sum_range_succ, ih]
    simp

/-- Bridge: prefix sums of a range-map list are Finset range sums. -/
theorem pushSum_take_range_map (g : ℕ → ℝ) {M P : ℕ} (h : M ≤ P) :
    pushSum (((List.range P).map g).take M) = ∑ m ∈ Finset.range M, g m := by
  rw [pushSum_eq_sum, ← List.map_take, List.take_range, Nat.min_eq_left h]
  exact sum_map_range g M

/-- The exact closed form: the rotation walk's prefix sum is the circle
chord r·cos γ − r·cos(γ + Mθ). -/
theorem sum_cos_closed_form {θ β r γ : ℝ}
    (hpolar : Complex.exp ((β : ℂ) * Complex.I)
        / (1 - Complex.exp ((θ : ℂ) * Complex.I))
      = (r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I))
    (hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, Real.cos (β + m * θ)
      = r * Real.cos γ - r * Real.cos (γ + M * θ) := by
  set w : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hw
  set e : ℂ := Complex.exp ((β : ℂ) * Complex.I) with he
  -- complex form of the sum
  have hterm : ∀ m : ℕ,
      Real.cos (β + m * θ) = (e * w ^ m).re := by
    intro m
    have h1 : e * w ^ m
        = Complex.exp (((β + m * θ : ℝ) : ℂ) * Complex.I) := by
      rw [he, hw, ← Complex.exp_nat_mul, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [h1, Complex.exp_ofReal_mul_I_re]
  have hsum : ∑ m ∈ Finset.range M, Real.cos (β + m * θ)
      = (e * ∑ m ∈ Finset.range M, w ^ m).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun m _ => hterm m
  rw [hsum, geom_sum_eq hne M]
  -- e·(w^M − 1)/(w − 1) = z − z·w^M with z = e/(1−w)
  have hz : e * ((w ^ M - 1) / (w - 1))
      = (r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I)
        - ((r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I)) * w ^ M := by
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hne
    have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr fun hh => hne hh.symm
    have hz0 : e = ((r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I)) * (1 - w) := by
      rw [← hpolar, div_mul_cancel₀ _ h1w]
    rw [hz0]
    field_simp
    ring
  rw [hz]
  -- real parts
  have hzw : (((r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I)) * w ^ M).re
      = r * Real.cos (γ + M * θ) := by
    have h1 : ((r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I)) * w ^ M
        = (r : ℂ) * Complex.exp (((γ + M * θ : ℝ) : ℂ) * Complex.I) := by
      rw [hw, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [h1, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hz1 : ((r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I)).re
      = r * Real.cos γ := by
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [Complex.sub_re, hzw, hz1]

/-- Within one wrap the orbit angle enters the up-window: some index M ≥ 1
with M·θ ≤ 2π + θ and cos(γ + Mθ) ≥ cos(θ/2). -/
theorem exists_orbit_cos_ge {θ γ : ℝ} (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : ℝ) * θ ≤ 2 * Real.pi + 2 * θ ∧
      Real.cos (θ / 2) ≤ Real.cos (γ + M * θ) := by
  -- the walk of angles x_M = γ + Mθ; target window center 2πk above x_1
  set k : ℤ := ⌊(γ + θ) / (2 * Real.pi)⌋ + 1 with hk
  set c : ℝ := (k : ℝ) * (2 * Real.pi) with hc
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hc1 : γ + θ < c := by
    have hfl := Int.lt_floor_add_one ((γ + θ) / (2 * Real.pi))
    have hkr : (γ + θ) / (2 * Real.pi) < (k : ℝ) := by
      simp only [hk]; push_cast; linarith
    have h' : γ + θ < (k : ℝ) * (2 * Real.pi) := by
      calc γ + θ = (γ + θ) / (2 * Real.pi) * (2 * Real.pi) := by field_simp
        _ < (k : ℝ) * (2 * Real.pi) := mul_lt_mul_of_pos_right hkr h2pi
    simpa [hc] using h'
  have hcup : c ≤ γ + θ + 2 * Real.pi := by
    have hfl := Int.floor_le ((γ + θ) / (2 * Real.pi))
    have hkr : (k : ℝ) ≤ (γ + θ) / (2 * Real.pi) + 1 := by
      simp only [hk]; push_cast; linarith
    have h' : (k : ℝ) * (2 * Real.pi) ≤ (γ + θ) + 2 * Real.pi := by
      calc (k : ℝ) * (2 * Real.pi)
          ≤ ((γ + θ) / (2 * Real.pi) + 1) * (2 * Real.pi) :=
            mul_le_mul_of_nonneg_right hkr h2pi.le
        _ = (γ + θ) + 2 * Real.pi := by field_simp
    simpa [hc] using h'
  -- angle walk ψ M = γ + Mθ, step exactly θ; first passage into [c, c+θ)
  set ψ : ℕ → ℝ := fun M => γ + M * θ with hψ
  have hstep : ∀ m : ℕ, ψ (m + 1) - ψ m ≤ θ := by
    intro m; simp only [hψ]; push_cast; ring_nf; linarith
  have hψ1 : ψ 1 < c := by simp only [hψ]; push_cast; linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, c ≤ ψ n := by
    refine ⟨1 + (⌈(2 * Real.pi) / θ⌉).toNat, ?_⟩
    have hnn : (0 : ℤ) ≤ ⌈(2 * Real.pi) / θ⌉ :=
      Int.ceil_nonneg (div_nonneg h2pi.le hθ0.le)
    have hcast : (((⌈(2 * Real.pi) / θ⌉).toNat : ℕ) : ℝ)
        = ((⌈(2 * Real.pi) / θ⌉ : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hnn)
    have hceil : (2 * Real.pi) / θ ≤ ((⌈(2 * Real.pi) / θ⌉ : ℤ) : ℝ) :=
      Int.le_ceil _
    have h2 : 2 * Real.pi ≤ (((⌈(2 * Real.pi) / θ⌉).toNat : ℕ) : ℝ) * θ := by
      rw [hcast]
      calc 2 * Real.pi = (2 * Real.pi) / θ * θ := by field_simp
        _ ≤ ((⌈(2 * Real.pi) / θ⌉ : ℤ) : ℝ) * θ :=
            mul_le_mul_of_nonneg_right hceil hθ0.le
    simp only [hψ]
    push_cast
    nlinarith
  -- shift to start at index 1 for the passage (so M ≥ 1)
  have hpass := exists_first_passage (ψ := fun i => ψ (1 + i)) (θmax := θ)
    (c := c) (fun m => by simpa only [Nat.add_assoc] using hstep (1 + m))
    (by simpa using hψ1)
    (n := n) (by simpa using le_trans hn (by
      have : ψ n ≤ ψ (1 + n) := by
        simp only [hψ]; push_cast; nlinarith
      exact this))
  obtain ⟨m, _, hm1, hm2⟩ := hpass
  set M₀ : ℕ := 1 + m with hM₀
  -- x = ψ M₀ ∈ [c, c + θ); pick M₀ or M₀ − 1 to land within θ/2 of c
  have hx1 : c ≤ ψ M₀ := hm1
  have hx2 : ψ M₀ < c + θ := hm2
  by_cases hhalf : ψ M₀ ≤ c + θ / 2
  · -- M₀ works: |ψ M₀ − c| ≤ θ/2
    refine ⟨M₀, by omega, ?_, ?_⟩
    · have : ψ M₀ ≤ γ + θ + 2 * Real.pi + θ / 2 := by linarith
      simp only [hψ] at this
      linarith
    · have habs : |ψ M₀ - c| ≤ θ / 2 := by
        rw [abs_le]; constructor <;> linarith
      have hcoseq : Real.cos (ψ M₀) = Real.cos (ψ M₀ - c) := by
        conv_lhs => rw [show ψ M₀ = (ψ M₀ - c) + (k : ℝ) * (2 * Real.pi) from by
          simp only [hc]; ring]
        rw [Real.cos_add_int_mul_two_pi]
      rw [hcoseq]
      have hcc : Real.cos (θ / 2) ≤ Real.cos |ψ M₀ - c| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
          (by linarith [Real.pi_pos]) habs
      rwa [Real.cos_abs] at hcc
  · -- M₀ − 1 = m works (note m could be 0: then ψ 0 = γ; but c − ψ m < θ/2
    -- and ψ m < c gives the same window; M must be ≥ 1, so use m if m ≥ 1,
    -- else fall back to M₀ (still within θ of c, cos ≥ cos θ ≥ ... no —
    -- m = 0 needs care: if m = 0 the passage started above; but ψ 1 < c ≤
    -- ψ (1+m) forces m ≥ 1 automatically).
    rw [not_le] at hhalf
    have hm0 : 1 ≤ m := by
      by_contra h0
      rw [not_le, Nat.lt_one_iff] at h0
      have hM1 : M₀ = 1 := by simp [hM₀, h0]
      rw [hM1] at hx1
      linarith [hψ1]
    refine ⟨m, hm0, ?_, ?_⟩
    · have hstep' : ψ M₀ - ψ m = θ := by
        simp only [hψ, hM₀]; push_cast; ring
      have : ψ m ≤ γ + θ + 2 * Real.pi := by linarith
      simp only [hψ] at this
      linarith
    · have hstep' : ψ M₀ - ψ m = θ := by
        simp only [hψ, hM₀]; push_cast; ring
      have habs : |ψ m - c| ≤ θ / 2 := by
        rw [abs_le]
        constructor <;> linarith
      have hcoseq : Real.cos (ψ m) = Real.cos (ψ m - c) := by
        conv_lhs => rw [show ψ m = (ψ m - c) + (k : ℝ) * (2 * Real.pi) from by
          simp only [hc]; ring]
        rw [Real.cos_add_int_mul_two_pi]
      rw [hcoseq]
      have hcc : Real.cos (θ / 2) ≤ Real.cos |ψ m - c| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
          (by linarith [Real.pi_pos]) habs
      rwa [Real.cos_abs] at hcc

/-- **The rotation first-wrap dip**: a misaligned rotation walk
(cos γ ≤ 1 − δ) takes, within one wrap, a prefix sum at most
−r·(δ − (1 − cos(θ/2))). -/
theorem rotation_dip {θ β r γ δ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi) (hr : 0 ≤ r)
    (hpolar : Complex.exp ((β : ℂ) * Complex.I)
        / (1 - Complex.exp ((θ : ℂ) * Complex.I))
      = (r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I))
    (hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1)
    (hmis : Real.cos γ ≤ 1 - δ) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : ℝ) * θ ≤ 2 * Real.pi + 2 * θ ∧
      ∑ m ∈ Finset.range M, Real.cos (β + m * θ)
        ≤ -(r * (δ - (1 - Real.cos (θ / 2)))) := by
  obtain ⟨M, hM1, hMb, hMcos⟩ := exists_orbit_cos_ge (γ := γ) hθ0 hθπ
  refine ⟨M, hM1, hMb, ?_⟩
  rw [sum_cos_closed_form hpolar hne M]
  have h1 : r * Real.cos γ ≤ r * (1 - δ) :=
    mul_le_mul_of_nonneg_left hmis hr
  have h2 : r * Real.cos (θ / 2) ≤ r * Real.cos (γ + M * θ) :=
    mul_le_mul_of_nonneg_left hMcos hr
  nlinarith

/-- **`dip_kills` from rotation data**: a birth whose future pushes are a
rotation walk (amplitude a, angles β + mθ) with misaligned start and depth
below the dip is killed. This is the constructor that discharges the
`MidCentralInput.dip_kills` field at lattice order. -/
theorem birthKilled_of_rotation {pushes : List ℝ} {birth : CascadeBirth}
    {θ β r γ δ a : ℝ} {P : ℕ}
    (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi) (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hdep : 0 < birth.depthSq)
    (hpush : futurePushes pushes birth
      = (List.range P).map fun m : ℕ => a * Real.cos (β + (m : ℝ) * θ))
    (hlen : 2 * Real.pi + 2 * θ ≤ (P : ℝ) * θ)
    (hpolar : Complex.exp ((β : ℂ) * Complex.I)
        / (1 - Complex.exp ((θ : ℂ) * Complex.I))
      = (r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I))
    (hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1)
    (hmis : Real.cos γ ≤ 1 - δ)
    (hdeep : birth.depthSq ≤ a * r * (δ - (1 - Real.cos (θ / 2)))) :
    BirthKilled pushes birth := by
  obtain ⟨M, _, hMb, hdip⟩ := rotation_dip hθ0 hθπ hr hpolar hne hmis
  have hMP : M ≤ P := by
    by_contra hcon
    rw [not_le] at hcon
    have : (P : ℝ) * θ < (M : ℝ) * θ := by
      have : (P : ℝ) < (M : ℝ) := by exact_mod_cast hcon
      exact mul_lt_mul_of_pos_right this hθ0
    linarith
  apply birthKilled_of_prefix_dip hdep
  refine ⟨(((List.range P).map fun m : ℕ => a * Real.cos (β + (m : ℝ) * θ)).take M),
    ?_, ?_⟩
  · rw [hpush]
    exact List.take_prefix _ _
  · rw [pushSum_take_range_map _ hMP]
    have hsum : ∑ m ∈ Finset.range M, a * Real.cos (β + m * θ)
        = a * ∑ m ∈ Finset.range M, Real.cos (β + m * θ) := by
      rw [Finset.mul_sum]
    rw [hsum]
    have := mul_le_mul_of_nonneg_left hdip ha
    nlinarith

end RHTower
