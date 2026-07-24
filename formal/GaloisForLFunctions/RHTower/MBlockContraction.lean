import GaloisForLFunctions.RHTower.MSpaceGainWindow

/-!
# The m-block contraction

On an m-block `(Y, 2QY]` with fibers above the uniform-ratio floor, the
log-weighted fiber remainder contracts against the trivial bound:

`∑_{Y < m ≤ 2QY} (2 log m + 2)·|R(⌊N/m⌋)|
   ≤ N·(a·ΔG − (a − ε')·(ρ/2)·log Y + 3a·E)`,

`ΔG = G(2QY) − G(Y)`, `G = log² + 2 log`, `E = (2 log(2QY) + 8)/Y`:
the gain window carries the pointwise ratio `ε'` and `G`-mass at least
`(ρ/2)·log Y`, the other zones carry the ambient ratio `a`, and each
zone's sharp window bound costs at most `E`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

set_option maxHeartbeats 1600000 in
theorem m_block_contraction {a δ ρ κ : ℝ} {Q Y N x₀ : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hQ1 : 1 ≤ Q) (hQ : 40 / δ + 2 < Real.log Q)
    (hY8 : 8 ≤ Y) (hYρ : 8 / ρ ≤ (Y : ℝ))
    (hN : 8 * Q * Y ≤ N)
    (hWρ : 2 / ρ ≤ ((N / (2 * Q * Y) : ℕ) : ℝ))
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ ≤ a)
    (hx₀ : x₀ ≤ N / (2 * Q * Y))
    (hratio : ∀ t : ℕ, x₀ ≤ t → |psiRemainder t| ≤ a * t)
    (hjunkf : ∀ t : ℕ, N / (2 * Q * Y) < t →
      Real.log ((Q * (N / (2 * Q * Y)) : ℕ) : ℝ) + 1
        + 2 * Real.sqrt t * Real.log t ≤ κ * t) :
    ∑ m ∈ Finset.Ioc Y (2 * Q * Y),
        (2 * Real.log m + 2) * |psiRemainder (N / m)|
      ≤ (N : ℝ) * (a * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ 2
            + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
          - (Real.log Y ^ 2 + 2 * Real.log Y))
        - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 2) * Real.log Y
        + 3 * a * ((2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y)) := by
  set ε' : ℝ := δ + ρ * (Real.log (1 / ρ) + 3) + κ with hε'
  have hε'0 : 0 ≤ ε' := by
    have hρlog0 : 0 ≤ Real.log (1 / ρ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hρ0, one_mul]; linarith)
    rw [hε']
    positivity
  obtain ⟨A, B, hYA, hAB, hB2QY, hgain, hpoint⟩ :=
    exists_m_gain_window hδ hρ0 hρ1 hκ hQ1 hQ hY8 hYρ hN hWρ hjunkf
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have h2QY0n : 0 < 2 * Q * Y :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have h2QY1 : 1 ≤ 2 * Q * Y := h2QY0n
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hY0R : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hlogY0 : 0 ≤ Real.log Y :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
  -- pointwise fiber ratio per zone
  have hfiber_ratio : ∀ m ∈ Finset.Ioc Y (2 * Q * Y),
      |psiRemainder (N / m)| ≤ a * ((N : ℝ) / m) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm0 : 0 < m := by omega
    have hm0R : (0 : ℝ) < m := by exact_mod_cast hm0
    have hfge : N / (2 * Q * Y) ≤ N / m :=
      Nat.div_le_div_left hm.2 hm0
    have hR := hratio (N / m) (le_trans hx₀ hfge)
    have hfl : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := by
      rw [le_div_iff₀ hm0R]
      exact_mod_cast Nat.div_mul_le_self N m
    calc |psiRemainder (N / m)| ≤ a * ((N / m : ℕ) : ℝ) := hR
      _ ≤ a * ((N : ℝ) / m) :=
        mul_le_mul_of_nonneg_left hfl ha.le
  have hgain_ratio : ∀ m ∈ Finset.Ioc A B,
      |psiRemainder (N / m)| ≤ ε' * ((N : ℝ) / m) := by
    intro m hm
    have hm' := hm
    rw [Finset.mem_Ioc] at hm'
    have hm0 : 0 < m := by omega
    have hm0R : (0 : ℝ) < m := by exact_mod_cast hm0
    have hfl : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := by
      rw [le_div_iff₀ hm0R]
      exact_mod_cast Nat.div_mul_le_self N m
    calc |psiRemainder (N / m)|
        ≤ ε' * ((N / m : ℕ) : ℝ) := hpoint m hm
      _ ≤ ε' * ((N : ℝ) / m) :=
        mul_le_mul_of_nonneg_left hfl hε'0
  -- per-zone weighted bounds
  have hw0 : ∀ m : ℕ, 1 ≤ m → (0 : ℝ) ≤ 2 * Real.log m + 2 := by
    intro m hm
    have := Real.log_nonneg (by exact_mod_cast hm : (1:ℝ) ≤ m)
    linarith
  have hzone : ∀ (r : ℝ), 0 ≤ r → ∀ (y z : ℕ), 2 ≤ y → y ≤ z →
      (∀ m ∈ Finset.Ioc y z, |psiRemainder (N / m)| ≤ r * ((N : ℝ) / m)) →
      ∑ m ∈ Finset.Ioc y z, (2 * Real.log m + 2) * |psiRemainder (N / m)|
        ≤ r * (N : ℝ) * ((Real.log z ^ 2 + 2 * Real.log z)
            - (Real.log y ^ 2 + 2 * Real.log y)
            + (2 * Real.log ((y : ℝ) + 1) + 6) / y) := by
    intro r hr y z hy hyz hrat
    have hterm : ∀ m ∈ Finset.Ioc y z,
        (2 * Real.log m + 2) * |psiRemainder (N / m)|
          ≤ r * (N : ℝ) * ((2 * Real.log m + 2) / m) := by
      intro m hm
      have hm' := hm
      rw [Finset.mem_Ioc] at hm'
      have hm0R : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      calc (2 * Real.log m + 2) * |psiRemainder (N / m)|
          ≤ (2 * Real.log m + 2) * (r * ((N : ℝ) / m)) :=
            mul_le_mul_of_nonneg_left (hrat m hm)
              (hw0 m (by omega))
        _ = r * (N : ℝ) * ((2 * Real.log m + 2) / m) := by
            field_simp
    calc ∑ m ∈ Finset.Ioc y z,
          (2 * Real.log m + 2) * |psiRemainder (N / m)|
        ≤ ∑ m ∈ Finset.Ioc y z,
            r * (N : ℝ) * ((2 * Real.log m + 2) / m) :=
          Finset.sum_le_sum hterm
      _ = r * (N : ℝ) * ∑ m ∈ Finset.Ioc y z,
            (2 * Real.log m + 2) / m := by
          rw [Finset.mul_sum]
      _ ≤ r * (N : ℝ) * ((Real.log z ^ 2 + 2 * Real.log z)
            - (Real.log y ^ 2 + 2 * Real.log y)
            + (2 * Real.log ((y : ℝ) + 1) + 6) / y) := by
          apply mul_le_mul_of_nonneg_left
            (sum_log_harmonic_window_le hy hyz) (by positivity)
  -- split the block into the three zones
  have hsplit : Finset.Ioc Y (2 * Q * Y)
      = Finset.Ioc Y A ∪ (Finset.Ioc A B ∪ Finset.Ioc B (2 * Q * Y)) := by
    rw [Finset.Ioc_union_Ioc_eq_Ioc hAB hB2QY,
      Finset.Ioc_union_Ioc_eq_Ioc (le_of_lt hYA) (le_trans hAB hB2QY)]
  have hd1 : Disjoint (Finset.Ioc Y A)
      (Finset.Ioc A B ∪ Finset.Ioc B (2 * Q * Y)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Ioc] at hx
    rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ioc] at hx'
    omega
  have hd2 : Disjoint (Finset.Ioc A B) (Finset.Ioc B (2 * Q * Y)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Ioc] at hx hx'
    omega
  rw [hsplit, Finset.sum_union hd1, Finset.sum_union hd2]
  -- zone instances
  have hz1 := hzone a ha.le Y A (by omega) (le_of_lt hYA)
    (fun m hm => hfiber_ratio m (by
      rw [Finset.mem_Ioc] at hm ⊢
      omega))
  have hz2 := hzone ε' hε'0 A B (by omega) hAB hgain_ratio
  have hz3 := hzone a ha.le B (2 * Q * Y) (by omega)
    hB2QY
    (fun m hm => hfiber_ratio m (by
      rw [Finset.mem_Ioc] at hm ⊢
      omega))
  -- error normalization: each zone error `≤ (2 log(2QY) + 8)/Y`
  have hEnorm : ∀ y : ℕ, Y ≤ y → y ≤ 2 * Q * Y →
      (2 * Real.log ((y : ℝ) + 1) + 6) / y
        ≤ (2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y := by
    intro y hy1 hy2
    have hy0R : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
    have h2QY0 : (0 : ℝ) < ((2 * Q * Y : ℕ) : ℝ) := by
      exact_mod_cast (by positivity : 0 < 2 * Q * Y)
    have hnum : 2 * Real.log ((y : ℝ) + 1) + 6
        ≤ 2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8 := by
      have h1 : Real.log ((y : ℝ) + 1)
          ≤ Real.log (((2 * Q * Y : ℕ) : ℝ) + 1) := by
        apply Real.log_le_log (by positivity)
        have : (y : ℝ) ≤ ((2 * Q * Y : ℕ) : ℝ) := by exact_mod_cast hy2
        linarith
      have h2 := log_succ_sub_log_le (j := 2 * Q * Y) h2QY1
      have h3 : (1 : ℝ) / ((2 * Q * Y : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one h2QY0]
        exact_mod_cast h2QY1
      linarith
    have hnum0 : 0 ≤ 2 * Real.log ((y : ℝ) + 1) + 6 := by
      have := Real.log_nonneg (show (1:ℝ) ≤ (y : ℝ) + 1 by linarith)
      linarith
    calc (2 * Real.log ((y : ℝ) + 1) + 6) / y
        ≤ (2 * Real.log ((y : ℝ) + 1) + 6) / Y := by
          apply div_le_div_of_nonneg_left hnum0 hY0R
          exact_mod_cast hy1
      _ ≤ (2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y := by
          apply div_le_div_of_nonneg_right _ hY0R.le
          exact hnum
  have hE1 := hEnorm Y le_rfl (by nlinarith [hQ1, hY8])
  have hE2 := hEnorm A (le_of_lt hYA) (le_trans hAB hB2QY)
  have hE3 := hEnorm B (le_trans (le_of_lt hYA) hAB) hB2QY
  -- gain mass lower bound
  have hgainmass : (ρ / 4) * (2 * Real.log Y)
      ≤ (Real.log B ^ 2 + 2 * Real.log B)
        - (Real.log A ^ 2 + 2 * Real.log A) := by
    have hlogA : Real.log Y ≤ Real.log A := by
      apply Real.log_le_log hY0R
      exact_mod_cast le_of_lt hYA
    have hlogAB : Real.log A ≤ Real.log B := by linarith [hgain, hρ0]
    have hfact : (Real.log B ^ 2 + 2 * Real.log B)
        - (Real.log A ^ 2 + 2 * Real.log A)
        = (Real.log B - Real.log A)
          * (Real.log B + Real.log A + 2) := by
      ring
    rw [hfact]
    have h1 : 2 * Real.log Y ≤ Real.log B + Real.log A + 2 := by
      linarith [hlogA, hlogAB, hlogY0]
    apply mul_le_mul hgain h1 (by linarith [hlogY0]) (by linarith [hρ0])
  -- combine
  have hεa : ε' ≤ a := by rw [hε']; exact hε'a
  have e1 : a * (N : ℝ) * ((Real.log A ^ 2 + 2 * Real.log A)
      - (Real.log Y ^ 2 + 2 * Real.log Y)
      + (2 * Real.log ((Y : ℝ) + 1) + 6) / Y)
      = a * (N:ℝ) * ((Real.log A ^ 2 + 2 * Real.log A)
        - (Real.log Y ^ 2 + 2 * Real.log Y))
        + a * (N:ℝ) * ((2 * Real.log ((Y : ℝ) + 1) + 6) / Y) := by ring
  have e2 : ε' * (N : ℝ) * ((Real.log B ^ 2 + 2 * Real.log B)
      - (Real.log A ^ 2 + 2 * Real.log A)
      + (2 * Real.log ((A : ℝ) + 1) + 6) / A)
      = ε' * (N:ℝ) * ((Real.log B ^ 2 + 2 * Real.log B)
        - (Real.log A ^ 2 + 2 * Real.log A))
        + ε' * (N:ℝ) * ((2 * Real.log ((A : ℝ) + 1) + 6) / A) := by ring
  have e3 : a * (N : ℝ) * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ 2
      + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
      - (Real.log B ^ 2 + 2 * Real.log B)
      + (2 * Real.log ((B : ℝ) + 1) + 6) / B)
      = a * (N:ℝ) * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ 2
        + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
        - (Real.log B ^ 2 + 2 * Real.log B))
        + a * (N:ℝ) * ((2 * Real.log ((B : ℝ) + 1) + 6) / B) := by ring
  have e4 : a * (N:ℝ) * ((Real.log A ^ 2 + 2 * Real.log A)
      - (Real.log Y ^ 2 + 2 * Real.log Y))
      + ε' * (N:ℝ) * ((Real.log B ^ 2 + 2 * Real.log B)
        - (Real.log A ^ 2 + 2 * Real.log A))
      + a * (N:ℝ) * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ 2
        + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
        - (Real.log B ^ 2 + 2 * Real.log B))
      = a * (N:ℝ) * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ 2
          + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
          - (Real.log Y ^ 2 + 2 * Real.log Y))
        - (a - ε') * (N:ℝ) * ((Real.log B ^ 2 + 2 * Real.log B)
          - (Real.log A ^ 2 + 2 * Real.log A)) := by ring
  have hgm : (a - ε') * (N:ℝ) * ((ρ / 4) * (2 * Real.log Y))
      ≤ (a - ε') * (N:ℝ) * ((Real.log B ^ 2 + 2 * Real.log B)
        - (Real.log A ^ 2 + 2 * Real.log A)) := by
    apply mul_le_mul_of_nonneg_left hgainmass
    apply mul_nonneg (by linarith) hNR.le
  have hgm2 : (a - ε') * (N:ℝ) * ((ρ / 4) * (2 * Real.log Y))
      = (N:ℝ) * ((a - ε') * (ρ / 2) * Real.log Y) := by ring
  have hEmul1 : a * (N:ℝ) * ((2 * Real.log ((Y : ℝ) + 1) + 6) / Y)
      ≤ a * (N:ℝ) * ((2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y) := by
    apply mul_le_mul_of_nonneg_left hE1 (by positivity)
  have hEmul2 : ε' * (N:ℝ) * ((2 * Real.log ((A : ℝ) + 1) + 6) / A)
      ≤ a * (N:ℝ) * ((2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y) := by
    have h1 : ε' * (N:ℝ) * ((2 * Real.log ((A : ℝ) + 1) + 6) / A)
        ≤ ε' * (N:ℝ) * ((2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y) := by
      apply mul_le_mul_of_nonneg_left hE2 (by positivity)
    have h2 : ε' * (N:ℝ) * ((2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y)
        ≤ a * (N:ℝ) * ((2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hεa hNR.le)
      have hlog2QY : 0 ≤ Real.log ((2 * Q * Y : ℕ) : ℝ) := by
        apply Real.log_nonneg
        exact_mod_cast h2QY1
      positivity
    linarith
  have hEmul3 : a * (N:ℝ) * ((2 * Real.log ((B : ℝ) + 1) + 6) / B)
      ≤ a * (N:ℝ) * ((2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y) := by
    apply mul_le_mul_of_nonneg_left hE3 (by positivity)
  have efinal : (N : ℝ) * (a * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ 2
        + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
      - (Real.log Y ^ 2 + 2 * Real.log Y))
      - (a - ε') * (ρ / 2) * Real.log Y
      + 3 * a * ((2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y))
      = a * (N:ℝ) * ((Real.log ((2 * Q * Y : ℕ) : ℝ) ^ 2
          + 2 * Real.log ((2 * Q * Y : ℕ) : ℝ))
          - (Real.log Y ^ 2 + 2 * Real.log Y))
        - (N:ℝ) * ((a - ε') * (ρ / 2) * Real.log Y)
        + 3 * (a * (N:ℝ)
          * ((2 * Real.log ((2 * Q * Y : ℕ) : ℝ) + 8) / Y)) := by
    ring
  linarith [hz1, hz2, hz3, e1, e2, e3, e4, hgm, hgm2, hEmul1, hEmul2,
    hEmul3, efinal]

end RHTower
