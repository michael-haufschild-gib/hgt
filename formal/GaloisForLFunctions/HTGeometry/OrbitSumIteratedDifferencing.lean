import GaloisForLFunctions.HTGeometry.ThreeFiveOrbitKorobovBound

/-!
# Korobov's bound by iterated differencing

For `g^{T₀} = 1 + X`, the shift-`h` autocorrelation of the orbit block
`l ↦ e(c gʲ (1 + X)ˡ/Q)` is again an orbit block, with coefficient
`c((1 + X)ʰ − 1) = c X Σ_{t<h}(1 + X)ᵗ` (`norm_orbitBlock_sq_le`).  Each differencing therefore
multiplies the coefficient by `X` and by a cofactor whose gcd with `D ∣ X` is at most `h`.  After
`r − 1` steps, `Q ∣ X^{r+1}` makes the blocks geometric.  Averaging over `j` then leaves complete
orbit sums, which vanish unless `D` divides the remaining cofactor (`orbitEnergy_terminal`).

* `orbitEnergy_le_korobovBeta`: induction over the depth, with exponents
  `β₀ = N^{r−1}/D + 1/N` and `β_{d+1} = 1/N + 2√β_d`.
* `norm_sum_orbit_sq_le_korobov`: `‖Σ_{i<T₀N} e(u gⁱ/Q)‖² ≤ T₀² N² β_{r−1}`.
* `korobovBeta_le`: `β_d ≤ 3ᵈ ε^{2^{−d}}` with `ε = N^{r−1}/D + 1/N ≤ 1`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.OrbitDifferencing

open StonehamParityDrift ThreeFiveOrbit

/-- The orbit block `Σ_{l<M} e(c gʲ (1 + X)ˡ / Q)`. -/
noncomputable def orbitBlock (Q : ℕ) (g X c : ℤ) (j M : ℕ) : ℂ :=
  ∑ l ∈ range M, ephase Q (c * g ^ j * (1 + X) ^ l)

/-- The energy `Σ_{j<T₀} ‖orbitBlock c j M‖²`. -/
noncomputable def orbitEnergy (Q T₀ : ℕ) (g X c : ℤ) (M : ℕ) : ℝ :=
  ∑ j ∈ range T₀, ‖orbitBlock Q g X c j M‖ ^ 2

/-- **Differencing an orbit block gives an orbit block.**  The shift-`h` autocorrelation of
`l ↦ e(c gʲ (1+X)ˡ/Q)` is the orbit block of the coefficient `c ((1 + X)ʰ − 1)`. -/
theorem norm_orbitBlock_sq_le (Q : ℕ) (g X c : ℤ) (j M : ℕ) :
    ‖orbitBlock Q g X c j M‖ ^ 2 ≤
      M + 2 * ∑ h ∈ Ico 1 M, ‖orbitBlock Q g X (c * ((1 + X) ^ h - 1)) j (M - h)‖ := by
  have hF : ∀ l, ‖ephase Q (c * g ^ j * (1 + X) ^ l)‖ ≤ 1 := fun l => (norm_ephase _ _).le
  have h := HTGeometry.weyl_differencing_bound M _ hF
  have e : ∀ h, HTGeometry.diffSum (fun l => ephase Q (c * g ^ j * (1 + X) ^ l)) M h =
      orbitBlock Q g X (c * ((1 + X) ^ h - 1)) j (M - h) := by
    intro h
    unfold HTGeometry.diffSum orbitBlock
    refine sum_congr rfl fun l _ => ?_
    rw [← ephase_neg, ← ephase_add]
    congr 1
    ring
  simp_rw [e] at h
  exact h

/-- `Σ_{j<T} aⱼ ≤ √(T Σ_{j<T} aⱼ²)`. -/
theorem sum_le_sqrt_card_mul_sum_sq (T : ℕ) (a : ℕ → ℝ) :
    ∑ j ∈ range T, a j ≤ Real.sqrt (T * ∑ j ∈ range T, a j ^ 2) := by
  refine Real.le_sqrt_of_sq_le ?_
  simpa using sq_sum_le_card_mul_sum_sq (s := range T) (f := a)

/-- **One differencing step for the energy.**  If every differenced energy is at most
`T₀ N² β`, then the energy is at most `T₀ N² (1/N + 2√β)`. -/
theorem orbitEnergy_le_step {Q T₀ N M : ℕ} {g X c : ℤ} (hN : 0 < N) (hM : M ≤ N) {β : ℝ}
    (hE : ∀ h ∈ Ico 1 M, orbitEnergy Q T₀ g X (c * ((1 + X) ^ h - 1)) (M - h) ≤
      T₀ * N ^ 2 * β) :
    orbitEnergy Q T₀ g X c M ≤ T₀ * N ^ 2 * (1 / N + 2 * Real.sqrt β) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (M : ℝ) ≤ N := by exact_mod_cast hM
  have hT : (0 : ℝ) ≤ T₀ := Nat.cast_nonneg _
  have hstep : ∀ h ∈ Ico 1 M, ∑ j ∈ range T₀,
      ‖orbitBlock Q g X (c * ((1 + X) ^ h - 1)) j (M - h)‖ ≤ T₀ * N * Real.sqrt β := by
    intro h hh
    refine (sum_le_sqrt_card_mul_sum_sq T₀ _).trans ?_
    calc Real.sqrt (T₀ * orbitEnergy Q T₀ g X (c * ((1 + X) ^ h - 1)) (M - h))
        ≤ Real.sqrt (T₀ * (T₀ * N ^ 2 * β)) := Real.sqrt_le_sqrt (by gcongr; exact hE h hh)
      _ = T₀ * N * Real.sqrt β := by
          rw [show (T₀ : ℝ) * (T₀ * N ^ 2 * β) = (T₀ * N) ^ 2 * β by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hcard : ((#(Ico 1 M) : ℕ) : ℝ) ≤ N := by
    simp only [Nat.card_Ico]; exact_mod_cast (Nat.sub_le M 1).trans hM
  calc orbitEnergy Q T₀ g X c M
      ≤ ∑ j ∈ range T₀, ((M : ℝ) + 2 * ∑ h ∈ Ico 1 M,
          ‖orbitBlock Q g X (c * ((1 + X) ^ h - 1)) j (M - h)‖) :=
        sum_le_sum fun j _ => norm_orbitBlock_sq_le Q g X c j M
    _ = T₀ * M + 2 * ∑ h ∈ Ico 1 M, ∑ j ∈ range T₀,
          ‖orbitBlock Q g X (c * ((1 + X) ^ h - 1)) j (M - h)‖ := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum, sum_comm]
    _ ≤ T₀ * N + 2 * ∑ _h ∈ Ico 1 M, (T₀ * N * Real.sqrt β : ℝ) := by
        gcongr with h hh
        exact hstep h hh
    _ = T₀ * N + 2 * ((#(Ico 1 M) : ℕ) * (T₀ * N * Real.sqrt β)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ T₀ * N + 2 * (N * (T₀ * N * Real.sqrt β)) := by gcongr
    _ = T₀ * N ^ 2 * (1 / N + 2 * Real.sqrt β) := by field_simp

/-! ### The terminal energy -/

/-- `(1 + X)ˡ ≡ 1 + l X (mod X²)`. -/
theorem one_add_pow_modEq_sq (X : ℤ) (l : ℕ) : (1 + X) ^ l ≡ 1 + l * X [ZMOD X ^ 2] := by
  have h := one_add_pow_modEq (Q := X ^ 2) (x := X) ⟨X, by ring⟩ l
  exact h.trans (Int.modEq_iff_dvd.mpr ⟨-(l.choose 2 : ℤ), by ring⟩)

/-- **Pair counting.**  At most `M gcd(D, W)/D + 1` indices `l' < M` satisfy `D ∣ W (l − l')`. -/
theorem card_filter_int_dvd_le {D : ℕ} (hD : 0 < D) (W : ℤ) (l M : ℕ) :
    (#{l' ∈ range M | (D : ℤ) ∣ W * ((l : ℤ) - ((l' : ℕ) : ℤ))} : ℝ) ≤
      M * Int.gcd D W / D + 1 := by
  obtain ⟨G, hG⟩ : ∃ G, G = Int.gcd D W := ⟨_, rfl⟩
  have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hG0 : 0 < G := hG ▸ Int.gcd_pos_of_ne_zero_left W hD0
  obtain ⟨E, hE⟩ : (G : ℤ) ∣ D := hG ▸ Int.gcd_dvd_left _ _
  obtain ⟨W', hW'⟩ : (G : ℤ) ∣ W := hG ▸ Int.gcd_dvd_right _ _
  have hGZ : (G : ℤ) ≠ 0 := by exact_mod_cast hG0.ne'
  have hcop : IsCoprime E W' := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_div_gcd_div_gcd (i := D) (j := W) (hG ▸ hG0)
    rwa [← hG, hE, hW', Int.mul_ediv_cancel_left _ hGZ, Int.mul_ediv_cancel_left _ hGZ] at this
  have hE0 : 0 < E := by
    have : (0 : ℤ) < D := by exact_mod_cast hD
    rw [hE] at this
    exact pos_of_mul_pos_right this (by positivity)
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, E = e := ⟨E.toNat, (Int.toNat_of_nonneg hE0.le).symm⟩
  have he0 : 0 < e := by exact_mod_cast hE0
  have hkey : ∀ l' ∈ ({l' ∈ range M | (D : ℤ) ∣ W * ((l : ℤ) - ((l' : ℕ) : ℤ))} : Finset ℕ),
      l' % e = l % e := by
    intro l' hl'
    rw [mem_filter] at hl'
    have h1 : (e : ℤ) ∣ W' * ((l : ℤ) - l') := by
      have hd := hl'.2
      rw [hE, hW', mul_assoc] at hd
      exact (mul_dvd_mul_iff_left hGZ).mp hd
    exact Nat.modEq_iff_dvd.mpr (IsCoprime.dvd_of_dvd_mul_left hcop h1)
  have hcard : #{l' ∈ range M | (D : ℤ) ∣ W * ((l : ℤ) - ((l' : ℕ) : ℤ))} ≤ M / e + 1 := by
    have := card_le_card_of_injOn (fun l' => l' / e)
      (s := ({l' ∈ range M | (D : ℤ) ∣ W * ((l : ℤ) - ((l' : ℕ) : ℤ))} : Finset ℕ))
      (t := range (M / e + 1))
      (fun l' hl' => by
        have hl'' := (mem_filter.mp hl').1
        rw [mem_range] at hl''
        simp only [coe_range, Set.mem_Iio]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hl''.le))
      (fun a ha b hb hab => by
        simp only at hab
        rw [← Nat.div_add_mod a e, ← Nat.div_add_mod b e, hab, hkey a ha, hkey b hb])
    simpa using this
  have hDG : (D : ℝ) = e * G := by
    have : (D : ℤ) = e * G := by rw [hE]; ring
    exact_mod_cast this
  have he0r : (0 : ℝ) < e := by exact_mod_cast he0
  have hG0r : (0 : ℝ) < G := by exact_mod_cast hG0
  rw [← hG]
  calc (#{l' ∈ range M | (D : ℤ) ∣ W * ((l : ℤ) - ((l' : ℕ) : ℤ))} : ℝ)
      ≤ ((M / e + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (M : ℝ) / e + 1 := by push_cast; gcongr; exact Nat.cast_div_le
    _ = M * G / D + 1 := by rw [hDG]; field_simp

/-- **The terminal energy.**  If `Q ∣ c X²`, the blocks are geometric, and averaging over `j`
leaves complete orbit sums; if these vanish unless `D ∣ W v`, the energy is at most
`T₀ M (M gcd(D, W)/D + 1)`. -/
theorem orbitEnergy_terminal {Q T₀ D : ℕ} {g X c W : ℤ} (hQ0 : Q ≠ 0) (hD : 0 < D)
    (hc : (Q : ℤ) ∣ c * X ^ 2)
    (hZ : ∀ v : ℤ, ∑ j ∈ range T₀, ephase Q (c * X * v * g ^ j) ≠ 0 → (D : ℤ) ∣ W * v)
    (M : ℕ) :
    orbitEnergy Q T₀ g X c M ≤ T₀ * (M * (M * Int.gcd D W / D + 1)) := by
  have hgeom : ∀ j, ‖orbitBlock Q g X c j M‖ = ‖∑ l ∈ range M, ephase Q ((c * X * g ^ j) * l)‖ := by
    intro j
    have hterm : ∀ l : ℕ, ephase Q (c * g ^ j * (1 + X) ^ l) =
        ephase Q (c * g ^ j) * ephase Q ((c * X * g ^ j) * l) := by
      intro l
      rw [← ephase_add]
      apply ephase_congr hQ0
      have h1 := ((one_add_pow_modEq_sq X l).mul_left' (c := c * g ^ j)).of_dvd
        (show (Q : ℤ) ∣ c * g ^ j * X ^ 2 from (hc.trans ⟨g ^ j, by ring⟩))
      have e : c * g ^ j * (1 + (l : ℤ) * X) = c * g ^ j + c * X * g ^ j * l := by ring
      rw [e] at h1
      exact h1
    rw [orbitBlock, sum_congr rfl fun l _ => hterm l, ← mul_sum, norm_mul, norm_ephase, one_mul]
  have hkey : ((orbitEnergy Q T₀ g X c M : ℝ) : ℂ) = ∑ l ∈ range M, ∑ l' ∈ range M,
      ∑ j ∈ range T₀, ephase Q (c * X * ((l : ℤ) - l') * g ^ j) := by
    unfold orbitEnergy
    simp_rw [hgeom]
    rw [Complex.ofReal_sum]
    simp_rw [norm_sum_ephase_sq]
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun l' _ => sum_congr rfl fun j _ => ?_
    congr 1
    ring
  have hZb : ∀ l l' : ℕ, ‖∑ j ∈ range T₀, ephase Q (c * X * ((l : ℤ) - l') * g ^ j)‖ ≤
      if (D : ℤ) ∣ W * ((l : ℤ) - ((l' : ℕ) : ℤ)) then (T₀ : ℝ) else 0 := by
    intro l l'
    split_ifs with hd
    · refine (norm_sum_le _ _).trans ?_
      simp [norm_ephase]
    · have : ∑ j ∈ range T₀, ephase Q (c * X * ((l : ℤ) - l') * g ^ j) = 0 := by
        by_contra hS
        exact hd (hZ _ hS)
      rw [this, norm_zero]
  have hnn : (0 : ℝ) ≤ orbitEnergy Q T₀ g X c M := by unfold orbitEnergy; positivity
  calc orbitEnergy Q T₀ g X c M = ‖((orbitEnergy Q T₀ g X c M : ℝ) : ℂ)‖ :=
        (Complex.norm_of_nonneg hnn).symm
    _ ≤ ∑ l ∈ range M, ∑ l' ∈ range M,
          if (D : ℤ) ∣ W * ((l : ℤ) - ((l' : ℕ) : ℤ)) then (T₀ : ℝ) else 0 := by
        rw [hkey]
        refine (norm_sum_le _ _).trans (sum_le_sum fun l _ => ?_)
        exact (norm_sum_le _ _).trans (sum_le_sum fun l' _ => hZb l l')
    _ = T₀ * ∑ l ∈ range M,
          (#{l' ∈ range M | (D : ℤ) ∣ W * ((l : ℤ) - ((l' : ℕ) : ℤ))} : ℝ) := by
        rw [mul_sum]
        refine sum_congr rfl fun l _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ T₀ * ∑ _l ∈ range M, ((M : ℝ) * Int.gcd D W / D + 1) := by
        gcongr with l _
        exact card_filter_int_dvd_le hD W l M
    _ = T₀ * (M * (M * Int.gcd D W / D + 1)) := by rw [sum_const, card_range, nsmul_eq_mul]

/-! ### Iterated differencing -/

/-- The Korobov exponents `β₀ = N^{r−1}/D + 1/N` and `β_{d+1} = 1/N + 2√β_d`. -/
noncomputable def korobovBeta (N D r : ℕ) : ℕ → ℝ
  | 0 => (N : ℝ) ^ (r - 1) / D + 1 / N
  | d + 1 => 1 / N + 2 * Real.sqrt (korobovBeta N D r d)

/-- `(1 + X)ʰ − 1 = X Σ_{t<h} (1 + X)ᵗ`. -/
theorem one_add_pow_sub_one (X : ℤ) (h : ℕ) :
    (1 + X) ^ h - 1 = X * ∑ t ∈ range h, (1 + X) ^ t := by
  rw [← geom_sum_mul, add_sub_cancel_left, mul_comm]

/-- `Σ_{t<h} (1 + X)ᵗ ≡ h (mod X)`. -/
theorem geom_sum_one_add_modEq (X : ℤ) (h : ℕ) :
    ∑ t ∈ range h, (1 + X) ^ t ≡ h [ZMOD X] := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_range_succ, Nat.cast_succ]
    have h1 : (1 + X) ≡ 1 [ZMOD X] := Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    exact ih.add (by simpa using h1.pow h)

/-- If `D ∣ X`, then `gcd(D, Σ_{t<h}(1+X)ᵗ) ≤ h` for `h ≥ 1`. -/
theorem gcd_geom_sum_le {D : ℕ} {X : ℤ} (hDX : (D : ℤ) ∣ X) {h : ℕ} (hh : 0 < h) :
    Int.gcd D (∑ t ∈ range h, (1 + X) ^ t) ≤ h := by
  obtain ⟨k, hk⟩ := (Int.ModEq.of_dvd hDX (geom_sum_one_add_modEq X h)).symm.dvd
  rw [show ∑ t ∈ range h, (1 + X) ^ t = h + D * k by linarith, Int.gcd_add_mul_left_right,
    Int.gcd_natCast_natCast]
  exact Nat.gcd_le_right _ hh

theorem int_gcd_mul_le {D : ℕ} (hD : 0 < D) (W U : ℤ) :
    Int.gcd D (W * U) ≤ Int.gcd D W * Int.gcd D U := by
  simp only [Int.gcd_eq_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
  refine Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hD)
    (Nat.gcd_pos_of_pos_left _ hD)) (Nat.gcd_mul_right_dvd_mul_gcd _ _ _)

/-- **Iterated differencing for the energy.**  Under `D ∣ X`, `Q ∣ X^{r+1}` and the vanishing
hypothesis for complete orbit sums, every coefficient `u X^{r−1−d} W` with
`gcd(D, W) ≤ N^{r−1−d}` has energy at most `T₀ N² β_d` on every length `M ≤ N`. -/
theorem orbitEnergy_le_korobovBeta {Q T₀ D N r : ℕ} {g X u : ℤ} (hQ0 : Q ≠ 0) (hD : 0 < D)
    (hN : 0 < N) (hr : 1 ≤ r) (hDX : (D : ℤ) ∣ X) (hQX : (Q : ℤ) ∣ X ^ (r + 1))
    (hZ : ∀ v : ℤ, ∑ j ∈ range T₀, ephase Q (u * X ^ r * v * g ^ j) ≠ 0 → (D : ℤ) ∣ v) :
    ∀ d : ℕ, d ≤ r - 1 → ∀ W : ℤ, Int.gcd D W ≤ N ^ (r - 1 - d) → ∀ M ≤ N,
      orbitEnergy Q T₀ g X (u * X ^ (r - 1 - d) * W) M ≤ T₀ * N ^ 2 * korobovBeta N D r d := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  intro d
  induction d with
  | zero =>
    intro _ W hW M hM
    have hc : (Q : ℤ) ∣ u * X ^ (r - 1 - 0) * W * X ^ 2 :=
      hQX.trans ⟨u * W, by rw [show r + 1 = (r - 1 - 0) + 2 by omega, pow_add]; ring⟩
    have hZ' : ∀ v : ℤ, ∑ j ∈ range T₀, ephase Q (u * X ^ (r - 1 - 0) * W * X * v * g ^ j) ≠ 0 →
        (D : ℤ) ∣ W * v := by
      intro v hv
      apply hZ
      have e : ∀ j : ℕ, u * X ^ r * (W * v) * g ^ j = u * X ^ (r - 1 - 0) * W * X * v * g ^ j := by
        intro j
        have hr' : X ^ r = X ^ (r - 1 - 0) * X := by rw [← pow_succ]; congr 1; omega
        rw [hr']
        ring
      simpa only [e] using hv
    refine (orbitEnergy_terminal hQ0 hD hc hZ' M).trans ?_
    have hG : ((Int.gcd D W : ℕ) : ℝ) ≤ (N : ℝ) ^ (r - 1) := by exact_mod_cast hW
    have hMr : (M : ℝ) ≤ N := by exact_mod_cast hM
    calc (T₀ : ℝ) * (M * (M * Int.gcd D W / D + 1)) ≤ T₀ * (N * (N * N ^ (r - 1) / D + 1)) := by
          gcongr
      _ = T₀ * N ^ 2 * korobovBeta N D r 0 := by
          simp only [korobovBeta]
          field_simp
  | succ d ih =>
    intro hd W hW M hM
    have hstep := orbitEnergy_le_step (Q := Q) (T₀ := T₀) (g := g) (X := X)
      (c := u * X ^ (r - 1 - (d + 1)) * W) hN hM (β := korobovBeta N D r d) (fun h hh => by
        rw [mem_Ico] at hh
        have e : u * X ^ (r - 1 - (d + 1)) * W * ((1 + X) ^ h - 1) =
            u * X ^ (r - 1 - d) * (W * ∑ t ∈ range h, (1 + X) ^ t) := by
          rw [one_add_pow_sub_one, show r - 1 - d = (r - 1 - (d + 1)) + 1 by omega, pow_succ]
          ring
        rw [e]
        refine ih (by omega) _ ?_ (M - h) (by omega)
        calc Int.gcd D (W * ∑ t ∈ range h, (1 + X) ^ t)
            ≤ Int.gcd D W * Int.gcd D (∑ t ∈ range h, (1 + X) ^ t) := int_gcd_mul_le hD _ _
          _ ≤ N ^ (r - 1 - (d + 1)) * N :=
              Nat.mul_le_mul hW ((gcd_geom_sum_le hDX (by omega)).trans (by omega))
          _ = N ^ (r - 1 - d) := by rw [← pow_succ]; congr 1; omega)
    simpa only [korobovBeta] using hstep

/-- **Korobov's bound by iterated differencing.**  If `g^{T₀} = 1 + X`, `D ∣ X`,
`Q ∣ X^{r+1}` and complete orbit sums `Σ_{j<T₀} e(u X^r v gʲ/Q)` vanish unless `D ∣ v`, then
`‖Σ_{i<T₀N} e(u gⁱ/Q)‖² ≤ T₀² N² β_{r−1}`. -/
theorem norm_sum_orbit_sq_le_korobov {Q T₀ D N r : ℕ} {g X u : ℤ} (hQ0 : Q ≠ 0) (hD : 0 < D)
    (hN : 0 < N) (hr : 1 ≤ r) (hDX : (D : ℤ) ∣ X) (hQX : (Q : ℤ) ∣ X ^ (r + 1))
    (hT : g ^ T₀ = 1 + X)
    (hZ : ∀ v : ℤ, ∑ j ∈ range T₀, ephase Q (u * X ^ r * v * g ^ j) ≠ 0 → (D : ℤ) ∣ v) :
    ‖∑ i ∈ range (T₀ * N), ephase Q (u * g ^ i)‖ ^ 2 ≤
      (T₀ : ℝ) ^ 2 * N ^ 2 * korobovBeta N D r (r - 1) := by
  have hE := orbitEnergy_le_korobovBeta hQ0 hD hN hr hDX hQX hZ (r - 1) le_rfl 1
    (by simp) N le_rfl
  rw [Nat.sub_self, pow_zero, mul_one, mul_one] at hE
  have hblock : ∀ j, ∑ l ∈ range N, ephase Q (u * g ^ (j + T₀ * l)) = orbitBlock Q g X u j N := by
    intro j
    unfold orbitBlock
    refine sum_congr rfl fun l _ => ?_
    rw [pow_add, pow_mul, hT, mul_assoc]
  rw [sum_range_mul_eq_sum_sum, sum_congr rfl fun j _ => hblock j]
  calc ‖∑ j ∈ range T₀, orbitBlock Q g X u j N‖ ^ 2
      ≤ (∑ j ∈ range T₀, ‖orbitBlock Q g X u j N‖) ^ 2 := by gcongr; exact norm_sum_le _ _
    _ ≤ T₀ * orbitEnergy Q T₀ g X u N := by
        have := sq_sum_le_card_mul_sum_sq (s := range T₀) (f := fun j => ‖orbitBlock Q g X u j N‖)
        simpa [orbitEnergy] using this
    _ ≤ T₀ * (T₀ * N ^ 2 * korobovBeta N D r (r - 1)) := by gcongr
    _ = (T₀ : ℝ) ^ 2 * N ^ 2 * korobovBeta N D r (r - 1) := by ring

/-- **Size of the Korobov exponents.**  If `ε = N^{r−1}/D + 1/N ≤ 1`, then
`β_d ≤ 3ᵈ ε^{2^{−d}}`. -/
theorem korobovBeta_le {N D r : ℕ} (hN : 0 < N) (hD : 0 < D)
    (hε : (N : ℝ) ^ (r - 1) / D + 1 / N ≤ 1) (d : ℕ) :
    korobovBeta N D r d ≤ 3 ^ d * ((N : ℝ) ^ (r - 1) / D + 1 / N) ^ ((1 / 2 : ℝ) ^ d) := by
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (N : ℝ) ^ (r - 1) / D + 1 / N := ⟨_, rfl⟩
  rw [← hεdef] at hε ⊢
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hNε : 1 / (N : ℝ) ≤ ε := by
    have : (0 : ℝ) ≤ (N : ℝ) ^ (r - 1) / D := by positivity
    rw [hεdef]
    linarith
  induction d with
  | zero => simp [korobovBeta, hεdef]
  | succ d ih =>
    simp only [korobovBeta]
    have hpow : ε ≤ ε ^ ((1 / 2 : ℝ) ^ (d + 1)) :=
      Real.self_le_rpow_of_le_one hε0 hε (pow_le_one₀ (by norm_num) (by norm_num))
    have hsq : Real.sqrt (3 ^ d * ε ^ ((1 / 2 : ℝ) ^ d)) ≤ 3 ^ d * ε ^ ((1 / 2 : ℝ) ^ (d + 1)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (ε ^ _), ← Real.rpow_mul hε0,
        ← pow_succ]
      gcongr
      rw [Real.sqrt_le_left (by positivity)]
      calc (3 : ℝ) ^ d ≤ 3 ^ d * 3 ^ d := le_mul_of_one_le_left (by positivity)
            (one_le_pow₀ (by norm_num))
        _ = (3 ^ d) ^ 2 := by ring
    have hpos : 0 ≤ ε ^ ((1 / 2 : ℝ) ^ (d + 1)) := by positivity
    calc 1 / (N : ℝ) + 2 * Real.sqrt (korobovBeta N D r d)
        ≤ ε + 2 * Real.sqrt (3 ^ d * ε ^ ((1 / 2 : ℝ) ^ d)) := by gcongr
      _ ≤ ε ^ ((1 / 2 : ℝ) ^ (d + 1)) + 2 * (3 ^ d * ε ^ ((1 / 2 : ℝ) ^ (d + 1))) := by gcongr
      _ ≤ 3 ^ (d + 1) * ε ^ ((1 / 2 : ℝ) ^ (d + 1)) := by
          have : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
          rw [pow_succ (3 : ℝ) d]
          nlinarith [mul_nonneg (sub_nonneg.mpr this) hpos]

end GaloisForLFunctions.HTGeometry.OrbitDifferencing
