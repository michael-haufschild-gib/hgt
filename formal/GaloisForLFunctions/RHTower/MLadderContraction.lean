import GaloisForLFunctions.RHTower.MBlockContraction

/-!
# The m-ladder contraction

Summing the per-block m-contraction over the geometric ladder
`Y_j = x₁·(2Q)^j` and converting each block's absolute gain into a
uniform coefficient contraction:

`∑_{x₁ < m ≤ x₁(2Q)^{J+1}} (2 log m + 2)·|R(⌊N/m⌋)|
   ≤ N·((a − θ)·(G(x₁(2Q)^{J+1}) − G(x₁)) + (J+1)·3a·(2 log N + 8)/x₁)`,

`G = log² + 2 log`, `θ = (a − ε')·ρ/(8·log(2Q))`.  A block's `G`-mass is
`log(2Q)·(2 log Y + log(2Q) + 2) ≤ 4·log(2Q)·log Y` once
`log(2Q) + 2 ≤ 2 log x₁`, so the gain `(a − ε')·(ρ/2)·log Y` from the
block's window dominates `θ` times the block mass uniformly in the level.
The junk-absorption, ratio-floor, and width hypotheses are stated at the
top block and propagate down the ladder by antitonicity of `⌊N/·⌋`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

set_option maxHeartbeats 1600000 in
theorem m_ladder_contraction {a δ ρ κ : ℝ} {Q x₀ x₁ N : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hQ1 : 1 ≤ Q) (hQ : 40 / δ + 2 < Real.log Q)
    (hx₁8 : 8 ≤ x₁) (hx₁ρ : 8 / ρ ≤ (x₁ : ℝ))
    (hx₁Q : Real.log ((2 * Q : ℕ) : ℝ) + 2 ≤ 2 * Real.log x₁)
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ ≤ a)
    (hratio : ∀ t : ℕ, x₀ ≤ t → |psiRemainder t| ≤ a * t) :
    ∀ J : ℕ,
      8 * Q * (x₁ * (2 * Q) ^ J) ≤ N →
      2 / ρ ≤ ((N / (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ) →
      x₀ ≤ N / (2 * Q * (x₁ * (2 * Q) ^ J)) →
      (∀ t : ℕ, N / (2 * Q * (x₁ * (2 * Q) ^ J)) < t →
        Real.log N + 1 + 2 * Real.sqrt t * Real.log t ≤ κ * t) →
      ∑ m ∈ Finset.Ioc x₁ (x₁ * (2 * Q) ^ (J + 1)),
          (2 * Real.log m + 2) * |psiRemainder (N / m)|
        ≤ (N : ℝ) * ((a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * ρ
              / (8 * Real.log ((2 * Q : ℕ) : ℝ)))
            * ((Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ (2 : ℕ)
                + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
              - (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁))
          + ((J : ℝ) + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))) := by
  set ε' : ℝ := δ + ρ * (Real.log (1 / ρ) + 3) + κ with hε'
  set L : ℝ := Real.log ((2 * Q : ℕ) : ℝ) with hL
  set θ : ℝ := (a - ε') * ρ / (8 * L) with hθ
  have hεa : ε' ≤ a := hε'a
  have hL0 : 0 < L := by
    rw [hL]
    apply Real.log_pos
    have : (2 : ℝ) ≤ ((2 * Q : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ 2 * Q)
    linarith
  have hx₁0 : 0 < x₁ := by omega
  have hx₁0R : (0 : ℝ) < x₁ := by exact_mod_cast hx₁0
  have hlogx₁0 : 0 ≤ Real.log x₁ :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x₁))
  have hYpos : ∀ j : ℕ, 1 ≤ x₁ * (2 * Q) ^ j := by
    intro j
    have h1 : 0 < (2 * Q) ^ j := pow_pos (by omega) j
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hx₁Y : ∀ j : ℕ, x₁ ≤ x₁ * (2 * Q) ^ j := by
    intro j
    exact Nat.le_mul_of_pos_right x₁ (pow_pos (by omega) j)
  -- per-block contraction, converted to the uniform coefficient `a − θ`
  have hblockconv : ∀ Y : ℕ, x₁ ≤ Y → 8 * Q * Y ≤ N →
      2 / ρ ≤ ((N / (2 * Q * Y) : ℕ) : ℝ) →
      x₀ ≤ N / (2 * Q * Y) →
      (∀ t : ℕ, N / (2 * Q * Y) < t →
        Real.log N + 1 + 2 * Real.sqrt t * Real.log t ≤ κ * t) →
      ∑ m ∈ Finset.Ioc Y (2 * Q * Y),
          (2 * Real.log m + 2) * |psiRemainder (N / m)|
        ≤ (N : ℝ) * ((a - θ)
            * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ (2 : ℕ)
                + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
              - (Real.log Y ^ (2 : ℕ) + 2 * Real.log Y))
          + 3 * a * ((2 * Real.log N + 8) / x₁)) := by
    intro Y hx₁Y' hNY hWρY hx₀Y hjunkUY
    have hY8 : 8 ≤ Y := le_trans hx₁8 hx₁Y'
    have hY0 : 0 < Y := by omega
    have hY0R : (0 : ℝ) < Y := by exact_mod_cast hY0
    have hYρ' : 8 / ρ ≤ (Y : ℝ) :=
      le_trans hx₁ρ (by exact_mod_cast hx₁Y')
    -- the block junk hypothesis from the uniform one
    have hW1 : 1 ≤ N / (2 * Q * Y) := by
      have h4 : (4 : ℝ) ≤ 2 / ρ := by
        rw [le_div_iff₀ hρ0]
        linarith
      have h1 : (1 : ℝ) ≤ ((N / (2 * Q * Y) : ℕ) : ℝ) := by linarith
      exact_mod_cast h1
    have hQW1 : 1 ≤ Q * (N / (2 * Q * Y)) :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have hQW_le : Q * (N / (2 * Q * Y)) ≤ N := by
      calc Q * (N / (2 * Q * Y))
          ≤ (2 * Q * Y) * (N / (2 * Q * Y)) := by
            apply Nat.mul_le_mul_right
            calc Q ≤ 2 * Q := by omega
              _ ≤ 2 * Q * Y := Nat.le_mul_of_pos_right (2 * Q) hY0
        _ = (N / (2 * Q * Y)) * (2 * Q * Y) := Nat.mul_comm _ _
        _ ≤ N := Nat.div_mul_le_self N (2 * Q * Y)
    have hjunkf : ∀ t : ℕ, N / (2 * Q * Y) < t →
        Real.log ((Q * (N / (2 * Q * Y)) : ℕ) : ℝ) + 1
          + 2 * Real.sqrt t * Real.log t ≤ κ * t := by
      intro t ht
      have h1 := hjunkUY t ht
      have hx : (1 : ℝ) ≤ ((Q * (N / (2 * Q * Y)) : ℕ) : ℝ) := by
        exact_mod_cast hQW1
      have h2 : Real.log ((Q * (N / (2 * Q * Y)) : ℕ) : ℝ) ≤ Real.log N :=
        Real.log_le_log (by linarith) (by exact_mod_cast hQW_le)
      linarith
    have hblock := m_block_contraction ha hδ hρ0 hρ1 hκ hQ1 hQ hY8 hYρ'
      hNY hWρY hε'a hx₀Y hratio hjunkf
    rw [← hε'] at hblock
    -- gain conversion: `θ · ΔG_block ≤ (a − ε')·(ρ/2)·log Y`
    have hcast2QY : ((2 * Q * Y : ℕ) : ℝ) = ((2 * Q : ℕ) : ℝ) * (Y : ℝ) := by
      push_cast
      ring
    have h2Q0R : (0 : ℝ) < ((2 * Q : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 2 * Q)
    have hlogsplit : Real.log ((2 * Q * Y : ℕ) : ℝ) = L + Real.log Y := by
      rw [hcast2QY, Real.log_mul (ne_of_gt h2Q0R) (ne_of_gt hY0R), hL]
    have hlogY : Real.log x₁ ≤ Real.log Y :=
      Real.log_le_log hx₁0R (by exact_mod_cast hx₁Y')
    have hΔG : (Real.log ((2 * Q * Y : ℕ) : ℝ) ^ (2 : ℕ)
          + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
        - (Real.log Y ^ (2 : ℕ) + 2 * Real.log Y)
        = L * (2 * Real.log Y + L + 2) := by
      rw [hlogsplit]
      ring
    have hLL : θ * (L * (2 * Real.log Y + L + 2))
        = (a - ε') * (ρ / 8) * (2 * Real.log Y + L + 2) := by
      rw [hθ]
      field_simp
    have hL2 : L + 2 ≤ 2 * Real.log Y := by linarith [hx₁Q, hlogY]
    have hkey : 0 ≤ (a - ε') * ρ * (2 * Real.log Y - (L + 2)) :=
      mul_nonneg (mul_nonneg (by linarith) hρ0.le) (by linarith)
    have hid : (a - ε') * (ρ / 2) * Real.log Y
        - (a - ε') * (ρ / 8) * (2 * Real.log Y + L + 2)
        = (a - ε') * ρ * (2 * Real.log Y - (L + 2)) / 8 := by
      ring
    have hθG : θ * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ (2 : ℕ)
          + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
        - (Real.log Y ^ (2 : ℕ) + 2 * Real.log Y))
        ≤ (a - ε') * (ρ / 2) * Real.log Y := by
      rw [hΔG, hLL]
      linarith [hkey, hid]
    -- error normalization to the ladder-uniform `3a·(2 log N + 8)/x₁`
    have h2QYN : 2 * Q * Y ≤ N := by
      calc 2 * Q * Y ≤ 8 * Q * Y :=
            Nat.mul_le_mul_right Y (by omega)
        _ ≤ N := hNY
    have hlog2QY0 : 0 ≤ Real.log ((2 * Q * Y : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.2
        (Nat.mul_ne_zero (by omega) (by omega))
    have hlogN' : Real.log ((2 * Q * Y : ℕ) : ℝ) ≤ Real.log N :=
      Real.log_le_log (by rw [hcast2QY]; positivity)
        (by exact_mod_cast h2QYN)
    have herr : 3 * a * ((2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y)
        ≤ 3 * a * ((2 * Real.log N + 8) / x₁) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc (2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y
          ≤ (2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / x₁ := by
            apply div_le_div_of_nonneg_left (by linarith) hx₁0R
            exact_mod_cast hx₁Y'
        _ ≤ (2 * Real.log N + 8) / x₁ := by
            apply div_le_div_of_nonneg_right _ hx₁0R.le
            linarith
    have hexp : (a - θ) * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ (2 : ℕ)
          + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
        - (Real.log Y ^ (2 : ℕ) + 2 * Real.log Y))
        = a * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ (2 : ℕ)
            + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
          - (Real.log Y ^ (2 : ℕ) + 2 * Real.log Y))
          - θ * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ (2 : ℕ)
            + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
          - (Real.log Y ^ (2 : ℕ) + 2 * Real.log Y)) := by
      ring
    calc ∑ m ∈ Finset.Ioc Y (2 * Q * Y),
          (2 * Real.log m + 2) * |psiRemainder (N / m)|
        ≤ (N : ℝ) * (a * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ (2 : ℕ)
              + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
            - (Real.log Y ^ (2 : ℕ) + 2 * Real.log Y))
          - (a - ε') * (ρ / 2) * Real.log Y
          + 3 * a * ((2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y)) :=
          hblock
      _ ≤ (N : ℝ) * ((a - θ)
            * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ (2 : ℕ)
                + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
              - (Real.log Y ^ (2 : ℕ) + 2 * Real.log Y))
          + 3 * a * ((2 * Real.log N + 8) / x₁)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
          linarith [hθG, herr, hexp]
  -- the ladder induction
  intro J
  induction J with
  | zero =>
    intro hN hWρ hx₀J hjunkU
    simp only [pow_zero, mul_one] at hN hWρ hx₀J hjunkU
    have hconv := hblockconv x₁ le_rfl hN hWρ hx₀J hjunkU
    have hYY : x₁ * (2 * Q) ^ (0 + 1) = 2 * Q * x₁ := by ring
    rw [hYY]
    simp only [Nat.cast_zero, zero_add, one_mul]
    exact hconv
  | succ J ih =>
    intro hN hWρ hx₀J hjunkU
    -- hypotheses propagate down the ladder
    have hmono : x₁ * (2 * Q) ^ J ≤ x₁ * (2 * Q) ^ (J + 1) :=
      Nat.mul_le_mul le_rfl
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hmono2 : 2 * Q * (x₁ * (2 * Q) ^ J)
        ≤ 2 * Q * (x₁ * (2 * Q) ^ (J + 1)) :=
      Nat.mul_le_mul le_rfl hmono
    have hpos2 : 0 < 2 * Q * (x₁ * (2 * Q) ^ J) := by
      have := hYpos J
      apply Nat.mul_pos (by omega) (by omega)
    have hdivmono : N / (2 * Q * (x₁ * (2 * Q) ^ (J + 1)))
        ≤ N / (2 * Q * (x₁ * (2 * Q) ^ J)) :=
      Nat.div_le_div_left hmono2 hpos2
    have hNJ : 8 * Q * (x₁ * (2 * Q) ^ J) ≤ N :=
      le_trans (Nat.mul_le_mul le_rfl hmono) hN
    have hWρJ : 2 / ρ ≤ ((N / (2 * Q * (x₁ * (2 * Q) ^ J)) : ℕ) : ℝ) :=
      le_trans hWρ (by exact_mod_cast hdivmono)
    have hx₀J' : x₀ ≤ N / (2 * Q * (x₁ * (2 * Q) ^ J)) :=
      le_trans hx₀J hdivmono
    have hjunkUJ : ∀ t : ℕ, N / (2 * Q * (x₁ * (2 * Q) ^ J)) < t →
        Real.log N + 1 + 2 * Real.sqrt t * Real.log t ≤ κ * t :=
      fun t ht => hjunkU t (lt_of_le_of_lt hdivmono ht)
    have IH := ih hNJ hWρJ hx₀J' hjunkUJ
    -- the top block
    have hblocktop := hblockconv (x₁ * (2 * Q) ^ (J + 1)) (hx₁Y (J + 1))
      hN hWρ hx₀J hjunkU
    -- split the ladder
    have hYY : x₁ * (2 * Q) ^ (J + 1 + 1)
        = 2 * Q * (x₁ * (2 * Q) ^ (J + 1)) := by ring
    have hY2QY : x₁ * (2 * Q) ^ (J + 1)
        ≤ 2 * Q * (x₁ * (2 * Q) ^ (J + 1)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hsplit : Finset.Ioc x₁ (2 * Q * (x₁ * (2 * Q) ^ (J + 1)))
        = Finset.Ioc x₁ (x₁ * (2 * Q) ^ (J + 1))
          ∪ Finset.Ioc (x₁ * (2 * Q) ^ (J + 1))
              (2 * Q * (x₁ * (2 * Q) ^ (J + 1))) :=
      (Finset.Ioc_union_Ioc_eq_Ioc (hx₁Y (J + 1)) hY2QY).symm
    have hdisj : Disjoint (Finset.Ioc x₁ (x₁ * (2 * Q) ^ (J + 1)))
        (Finset.Ioc (x₁ * (2 * Q) ^ (J + 1))
          (2 * Q * (x₁ * (2 * Q) ^ (J + 1)))) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_Ioc] at hx hx'
      omega
    rw [hYY, hsplit, Finset.sum_union hdisj]
    calc (∑ m ∈ Finset.Ioc x₁ (x₁ * (2 * Q) ^ (J + 1)),
          (2 * Real.log m + 2) * |psiRemainder (N / m)|)
        + ∑ m ∈ Finset.Ioc (x₁ * (2 * Q) ^ (J + 1))
            (2 * Q * (x₁ * (2 * Q) ^ (J + 1))),
            (2 * Real.log m + 2) * |psiRemainder (N / m)|
        ≤ ((N : ℝ) * ((a - θ)
            * ((Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ (2 : ℕ)
                + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ))
              - (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁))
          + ((J : ℝ) + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))))
          + (N : ℝ) * ((a - θ)
            * ((Real.log ((2 * Q * (x₁ * (2 * Q) ^ (J + 1)) : ℕ) : ℝ) ^ (2 : ℕ)
                + 2 * Real.log
                  ((2 * Q * (x₁ * (2 * Q) ^ (J + 1)) : ℕ) : ℝ))
              - (Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) ^ (2 : ℕ)
                + 2 * Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ)))
          + 3 * a * ((2 * Real.log N + 8) / x₁)) :=
          add_le_add IH hblocktop
      _ = (N : ℝ) * ((a - θ)
            * ((Real.log ((2 * Q * (x₁ * (2 * Q) ^ (J + 1)) : ℕ) : ℝ) ^ (2 : ℕ)
                + 2 * Real.log
                  ((2 * Q * (x₁ * (2 * Q) ^ (J + 1)) : ℕ) : ℝ))
              - (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁))
          + (((J + 1 : ℕ) : ℝ) + 1)
            * (3 * a * ((2 * Real.log N + 8) / x₁))) := by
          push_cast
          ring

end RHTower
