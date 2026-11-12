import GaloisForLFunctions.LogarithmicChowla.DilatedWindows
import GaloisForLFunctions.MatomakiRadziwill.LiouvilleShortSums
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# (MR) for the twisted windows `V(b/s, T)`

For `s ≥ 1` and `θ = b/s` (`tendsto_twistVar_zero`): `V(θ, T) = L(|T^{-1}Σ_{u<T} λ(n+u)e(uθ)|²) → 0`
as `T → ∞`, for every ultrafilter `U ≤ atTop`.

* (A3) `e(mθ)` depends on `m mod s`, so `|Σ_u λ(n+u)e(uθ)|² ≤ s Σ_{r<s} |V_r|²`, `V_r` the sum over
  `m = n+u ≡ r` (`normSq_twist_le`).  With `g = (r, s)`, `q = s/g`, `a = r/g`:
  `m ≡ r (s) ⟺ g | m ∧ m/g ≡ a (q)` (`mod_eq_iff`), and orthogonality of the characters mod `q`
  gives `V_r = λ(g) φ(q)^{-1} Σ_χ χ(a)^{-1} Σ_{n ≤ gm < n+T} λχ(m)` (`classSum_eq`).
* (A4) `λχ₀(m) = Σ_{e|q} μ(e)λ(e) 1_{e|m} λ(m/e)`, so the principal windows are dilated windows of
  `λ` (`norm_dilWin_principal_le`).
* (A5) (A2) for `λχ`, `χ ≠ 1` (`exists_short_sum_mean_square_twLiouville_le`) and for `λ`
  (`exists_short_sum_mean_square_liouville_le`).
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Filter Topology GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

variable {U : Ultrafilter ℝ}

/-- `Σ_{u<T, g | n+u} F((n+u)/g)` is the dilated window. -/
theorem sum_filter_dvd_eq_dilWin (F : ℕ → ℂ) {g : ℕ} (hg : 1 ≤ g) (n T : ℕ) :
    ∑ u ∈ (range T).filter (fun u => g ∣ n + u), F ((n + u) / g) = dilWin F g n T := by
  refine Finset.sum_nbij' (fun u => (n + u) / g) (fun m => g * m - n) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [mem_filter, mem_range] at hu
    obtain ⟨hu, k, hk⟩ := hu
    rw [mem_filter, mem_range, hk, Nat.mul_div_cancel_left k (by omega)]
    have hkle : k ≤ g * k := Nat.le_mul_of_pos_left k (by omega)
    omega
  · intro m hm
    rw [mem_filter, mem_range] at hm
    rw [mem_filter, mem_range]
    refine ⟨by omega, m, by omega⟩
  · intro u hu
    rw [mem_filter] at hu
    obtain ⟨-, k, hk⟩ := hu
    show g * ((n + u) / g) - n = u
    rw [hk, Nat.mul_div_cancel_left k (by omega)]
    omega
  · intro m hm
    rw [mem_filter] at hm
    show (n + (g * m - n)) / g = m
    have : n + (g * m - n) = g * m := by omega
    rw [this, Nat.mul_div_cancel_left m (by omega)]
  · intro u _; rfl

/-- **Residue classes mod `s` through the `g = (r, s)` layer.** -/
theorem mod_eq_iff {r s m : ℕ} (hs : 1 ≤ s) (hr : r < s) :
    m % s = r ↔ Nat.gcd r s ∣ m
      ∧ (((m / Nat.gcd r s : ℕ) : ZMod (s / Nat.gcd r s)) = ((r / Nat.gcd r s : ℕ) : ZMod _)) := by
  set g := Nat.gcd r s with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right r (by omega)
  have hgs : g ∣ s := Nat.gcd_dvd_right r s
  have hgr : g ∣ r := Nat.gcd_dvd_left r s
  obtain ⟨q, hq⟩ := hgs
  obtain ⟨a, ha⟩ := hgr
  have hqd : s / g = q := by rw [hq, Nat.mul_div_cancel_left q hg0]
  have had : r / g = a := by rw [ha, Nat.mul_div_cancel_left a hg0]
  rw [hqd, had]
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hq; omega
    · exact h
  have haq : a < q := by
    by_contra h
    push Not at h
    have : g * q ≤ g * a := Nat.mul_le_mul_left g h
    omega
  constructor
  · intro hm
    have hdiv := Nat.div_add_mod m s
    rw [hm] at hdiv
    refine ⟨⟨q * (m / s) + a, by rw [mul_add, ← mul_assoc, ← hq, ← ha]; omega⟩, ?_⟩
    have hmg : m / g = q * (m / s) + a := by
      rw [← Nat.mul_div_cancel_left (q * (m / s) + a) hg0]
      congr 1
      rw [mul_add, ← mul_assoc, ← hq, ← ha]; omega
    rw [hmg, ZMod.natCast_eq_natCast_iff', Nat.mul_add_mod]
  · rintro ⟨⟨k, hk⟩, hmod⟩
    rw [hk, Nat.mul_div_cancel_left k hg0, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt haq] at hmod
    have hkd := Nat.div_add_mod k q
    rw [hmod] at hkd
    have hm : m = s * (k / q) + r := by
      rw [hk, hq, ha]
      conv_lhs => rw [← hkd]
      ring
    rw [hm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem lam_cast (m : ℕ) : ((lam m : ℝ) : ℂ) = (ArithmeticFunction.liouville m : ℂ) := by
  rw [lam]; push_cast; rfl

/-- **One residue class, through the characters mod `q`.** -/
theorem classSum_eq {r s : ℕ} (hs : 1 ≤ s) (hr : r < s) (n T : ℕ) :
    ∑ u ∈ (range T).filter (fun u => (n + u) % s = r), ((lam (n + u) : ℝ) : ℂ)
      = (ArithmeticFunction.liouville (Nat.gcd r s) : ℂ) / ((s / Nat.gcd r s).totient : ℂ)
        * ∑ χ : DirichletCharacter ℂ (s / Nat.gcd r s),
            χ ((r / Nat.gcd r s : ℕ) : ZMod (s / Nat.gcd r s))⁻¹
              * dilWin (twLiouville χ) (Nat.gcd r s) n T := by
  set g := Nat.gcd r s with hg
  set q := s / g with hqdef
  set a := r / g with hadef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right r (by omega)
  have hq0 : 0 < q := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right r s)) hg0
  haveI : NeZero q := ⟨by omega⟩
  have hcop : Nat.Coprime a q := Nat.coprime_div_gcd_div_gcd hg0
  have haU : IsUnit ((a : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr hcop
  have hφ : ((q.totient : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
  -- the class indicator through the characters
  have hind : ∀ m : ℕ, (if ((m : ℕ) : ZMod q) = ((a : ℕ) : ZMod q) then (1 : ℂ) else 0)
      = ((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ℕ) : ZMod q)⁻¹ * χ ((m : ℕ) : ZMod q) := by
    intro m
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ haU]
    split_ifs with h1 h2 h2
    · field_simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  -- rewrite the class sum
  have h1 : ∑ u ∈ (range T).filter (fun u => (n + u) % s = r), ((lam (n + u) : ℝ) : ℂ)
      = ∑ u ∈ (range T).filter (fun u => g ∣ n + u),
          (ArithmeticFunction.liouville g : ℂ) * ((ArithmeticFunction.liouville ((n + u) / g) : ℂ)
            * (if (((n + u) / g : ℕ) : ZMod q) = ((a : ℕ) : ZMod q) then (1 : ℂ) else 0)) := by
    rw [sum_filter, sum_filter]
    refine sum_congr rfl fun u _ => ?_
    have hiff := mod_eq_iff (m := n + u) hs hr
    rw [← hg, ← hqdef, ← hadef] at hiff
    by_cases hd : g ∣ n + u
    · rw [if_pos hd]
      obtain ⟨k, hk⟩ := hd
      have hlam : ((lam (n + u) : ℝ) : ℂ) = (ArithmeticFunction.liouville g : ℂ)
          * (ArithmeticFunction.liouville ((n + u) / g) : ℂ) := by
        rw [lam_cast, hk, Nat.mul_div_cancel_left k hg0, ArithmeticFunction.liouville_apply_mul]
        push_cast; ring
      by_cases hc : (((n + u) / g : ℕ) : ZMod q) = ((a : ℕ) : ZMod q)
      · rw [if_pos (hiff.mpr ⟨⟨k, hk⟩, hc⟩), if_pos hc, hlam, mul_one]
      · have : ¬ (n + u) % s = r := fun h => hc (hiff.mp h).2
        rw [if_neg this, if_neg hc]; simp
    · have : ¬ (n + u) % s = r := fun h => hd (hiff.mp h).1
      rw [if_neg this, if_neg hd]
  rw [h1]
  simp_rw [hind]
  -- exchange the sums
  have e : ∀ u ∈ (range T).filter (fun u => g ∣ n + u),
      (ArithmeticFunction.liouville g : ℂ) * ((ArithmeticFunction.liouville ((n + u) / g) : ℂ)
        * (((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ℕ) : ZMod q)⁻¹ * χ ((((n + u) / g : ℕ) : ℕ) : ZMod q)))
      = (ArithmeticFunction.liouville g : ℂ) / ((q.totient : ℕ) : ℂ)
        * ∑ χ : DirichletCharacter ℂ q, χ ((a : ℕ) : ZMod q)⁻¹
          * twLiouville χ ((n + u) / g) := by
    intro u _
    rw [div_eq_mul_inv, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun χ _ => ?_
    rw [twLiouville]
    ring
  refine (Finset.sum_congr rfl e).trans ?_
  rw [← mul_sum, sum_comm]
  congr 1
  refine sum_congr rfl fun χ _ => ?_
  rw [← mul_sum, sum_filter_dvd_eq_dilWin _ hg0]

/-- `|V_r|² ≤ #χ · Σ_χ |dilWin λχ|²`. -/
theorem normSq_classSum_le {r s : ℕ} (hs : 1 ≤ s) (hr : r < s) (n T : ℕ) :
    ‖∑ u ∈ (range T).filter (fun u => (n + u) % s = r), ((lam (n + u) : ℝ) : ℂ)‖ ^ 2
      ≤ (Fintype.card (DirichletCharacter ℂ (s / Nat.gcd r s)) : ℝ)
        * ∑ χ : DirichletCharacter ℂ (s / Nat.gcd r s),
            ‖dilWin (twLiouville χ) (Nat.gcd r s) n T‖ ^ 2 := by
  set g := Nat.gcd r s with hg
  set q := s / g with hqdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right r (by omega)
  have hq0 : 0 < q := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right r s)) hg0
  haveI : NeZero q := ⟨by omega⟩
  rw [classSum_eq hs hr]
  have hφ1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hb : ‖(ArithmeticFunction.liouville g : ℂ) / ((q.totient : ℕ) : ℂ)
      * ∑ χ : DirichletCharacter ℂ q, χ (((r / g : ℕ) : ZMod q))⁻¹
        * dilWin (twLiouville χ) g n T‖
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖dilWin (twLiouville χ) g n T‖ := by
    rw [norm_mul]
    have hc : ‖(ArithmeticFunction.liouville g : ℂ) / ((q.totient : ℕ) : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast]
      have hl : ‖(ArithmeticFunction.liouville g : ℂ)‖ ≤ 1 := by
        rw [ArithmeticFunction.liouville_apply (by omega)]
        push_cast
        rw [norm_pow, norm_neg, norm_one, one_pow]
      rw [div_le_one (by linarith)]
      linarith
    have hs' : ‖∑ χ : DirichletCharacter ℂ q, χ (((r / g : ℕ) : ZMod q))⁻¹
        * dilWin (twLiouville χ) g n T‖ ≤ ∑ χ : DirichletCharacter ℂ q,
          ‖dilWin (twLiouville χ) g n T‖ := by
      refine le_trans (norm_sum_le _ _) (sum_le_sum fun χ _ => ?_)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
    calc ‖(ArithmeticFunction.liouville g : ℂ) / ((q.totient : ℕ) : ℂ)‖
          * ‖∑ χ : DirichletCharacter ℂ q, χ (((r / g : ℕ) : ZMod q))⁻¹
            * dilWin (twLiouville χ) g n T‖
        ≤ 1 * ∑ χ : DirichletCharacter ℂ q, ‖dilWin (twLiouville χ) g n T‖ :=
          mul_le_mul hc hs' (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have h3 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
    (f := fun χ => ‖dilWin (twLiouville χ) g n T‖)
  rw [Finset.card_univ] at h3
  exact le_trans h2 h3

/-- **(A3) The periodic twist splits into residue classes.** -/
theorem normSq_twist_le {s : ℕ} (hs : 1 ≤ s) (b n T : ℕ) :
    Complex.normSq (∑ u ∈ range T, (lam (n + u) : ℂ) * ex (u * ((b : ℝ) / s)))
      ≤ s * ∑ r ∈ range s,
          ‖∑ u ∈ (range T).filter (fun u => (n + u) % s = r), ((lam (n + u) : ℝ) : ℂ)‖ ^ 2 := by
  set θ : ℝ := (b : ℝ) / s with hθ
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  -- multiply by `e(nθ)`
  have hmul : (∑ u ∈ range T, (lam (n + u) : ℂ) * ex (u * θ)) * ex (n * θ)
      = ∑ u ∈ range T, (lam (n + u) : ℂ) * ex (((n + u : ℕ) : ℝ) * θ) := by
    rw [sum_mul]
    refine sum_congr rfl fun u _ => ?_
    rw [mul_assoc, ← ex_add]
    congr 2
    push_cast; ring
  have hnorm : Complex.normSq (∑ u ∈ range T, (lam (n + u) : ℂ) * ex (u * θ))
      = ‖∑ u ∈ range T, (lam (n + u) : ℂ) * ex (((n + u : ℕ) : ℝ) * θ)‖ ^ 2 := by
    rw [← hmul, norm_mul, norm_ex, mul_one, Complex.normSq_eq_norm_sq]
  rw [hnorm]
  -- group by the residue `r = (n+u) mod s`
  have hfib : ∑ u ∈ range T, (lam (n + u) : ℂ) * ex (((n + u : ℕ) : ℝ) * θ)
      = ∑ r ∈ range s, ex (r * θ)
          * ∑ u ∈ (range T).filter (fun u => (n + u) % s = r), ((lam (n + u) : ℝ) : ℂ) := by
    rw [← sum_fiberwise_of_maps_to (g := fun u => (n + u) % s)
      (fun u _ => mem_range.mpr (Nat.mod_lt _ (by omega)))]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun u hu => ?_
    rw [mem_filter] at hu
    have hper : ex (((n + u : ℕ) : ℝ) * θ) = ex (r * θ) := by
      have hdm := Nat.div_add_mod (n + u) s
      rw [hu.2] at hdm
      obtain ⟨K, hK⟩ : ∃ K, K = (n + u) / s := ⟨_, rfl⟩
      rw [← hK] at hdm
      have e : ((n + u : ℕ) : ℝ) = s * (K : ℝ) + r := by exact_mod_cast hdm.symm
      have : ((n + u : ℕ) : ℝ) * θ = (r : ℝ) * θ + ((K * b : ℕ) : ℤ) := by
        rw [Int.cast_natCast, Nat.cast_mul, e, hθ]
        field_simp
        ring
      rw [this, ex_add_int]
    rw [hper]; ring
  rw [hfib]
  have h1 : ‖∑ r ∈ range s, ex (r * θ)
      * ∑ u ∈ (range T).filter (fun u => (n + u) % s = r), ((lam (n + u) : ℝ) : ℂ)‖
      ≤ ∑ r ∈ range s,
        ‖∑ u ∈ (range T).filter (fun u => (n + u) % s = r), ((lam (n + u) : ℝ) : ℂ)‖ := by
    refine le_trans (norm_sum_le _ _) (le_of_eq (sum_congr rfl fun r _ => ?_))
    rw [norm_mul, norm_ex, one_mul]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 := sq_sum_le_card_mul_sum_sq (s := range s)
    (f := fun r => ‖∑ u ∈ (range T).filter (fun u => (n + u) % s = r), ((lam (n + u) : ℝ) : ℂ)‖)
  rw [card_range] at h3
  exact le_trans h2 h3

end

end GaloisForLFunctions.LogarithmicChowla
