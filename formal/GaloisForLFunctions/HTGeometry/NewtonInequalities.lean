import GaloisForLFunctions.HTGeometry.SignAlternationHyperbolicity

/-!
# Newton's inequalities

For a real polynomial `p` of degree `d` **all of whose roots are real**, write
`p = Σ_k C(d,k)·A_k·X^{d-k}`, i.e. `A_k = c_{d-k}/C(d,k)`.  Newton's inequalities say that the
normalised coefficient sequence is log-concave:

`A_{k-1}·A_{k+1} ≤ A_k²`  for `1 ≤ k ≤ d-1`.

mathlib has no version of this.  The proof here is the classical one, organised as a strong
induction on the degree around the two operations that preserve real-rootedness:

* **differentiation** (`hyperbolic_derivative`, immediate from mathlib's
  `Polynomial.card_roots_le_derivative`) sends `A_k ↦ d·A_k` and drops the top index
  (`newtonCoeff_derivative`), so it yields every index `k ≤ d-2` from the degree-`d-1` case;
* **reversal** (`hyperbolic_reverse`, via the splitting factorisation and
  `reverse (X - C r) = 1 - C r·X`) sends `A_k ↦ A_{d-k}` (`newtonCoeff_reverse`), which converts the
  one remaining index `k = d-1` into the index `1`, already covered when `d ≥ 3`.

The degree-two base case is the discriminant of a real-rooted quadratic; the degenerate branch
`p(0) = 0` is handled directly, since then `A_d = 0`.

## Main results

* `hyperbolic_derivative`, `hyperbolic_reverse` — real-rootedness is preserved;
* `newtonCoeff` — the normalised coefficient `A_k`;
* `newton_inequality` — **Newton's inequalities**.
-/

namespace GaloisForLFunctions.SignAlternation

open Polynomial

/-! ### Hyperbolicity is preserved by differentiation and by reversal -/

theorem hyperbolic_derivative {p : ℝ[X]} (hp : Hyperbolic p) : Hyperbolic (derivative p) := by
  unfold Hyperbolic at hp ⊢
  have h1 := Polynomial.card_roots_le_derivative p
  have h2 : Multiset.card (derivative p).roots ≤ (derivative p).natDegree :=
    Polynomial.card_roots' _
  have h3 := Polynomial.natDegree_derivative_le p
  omega

/-- `reverse` as a monoid hom on real polynomials. -/
noncomputable def reverseMonoidHom : ℝ[X] →* ℝ[X] where
  toFun := Polynomial.reverse
  map_one' := by simpa using Polynomial.reverse_C (1 : ℝ)
  map_mul' := Polynomial.reverse_mul_of_domain

theorem coeff_reverse_natDegree (p : ℝ[X]) : p.reverse.coeff p.natDegree = p.coeff 0 := by
  rw [Polynomial.coeff_reverse]
  simp

theorem natDegree_reverse_eq {p : ℝ[X]} (h0 : p.coeff 0 ≠ 0) :
    p.reverse.natDegree = p.natDegree := by
  refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero (by rw [coeff_reverse_natDegree]; exact h0))
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
  rw [Polynomial.coeff_reverse, Polynomial.revAt_eq_self_of_lt (by exact_mod_cast hn)]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hn)

theorem reverse_X_sub_C (r : ℝ) : (X - C r).reverse = 1 - C r * X := by
  ext n
  rw [Polynomial.coeff_reverse]
  have hd : (X - C r : ℝ[X]).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_sub_C r
  rw [hd]
  match n with
  | 0 => simp [Polynomial.revAt, Polynomial.coeff_one]
  | 1 => simp [Polynomial.revAt, Polynomial.coeff_one]
  | (k + 2) =>
      rw [Polynomial.revAt_eq_self_of_lt (by omega)]
      simp [Polynomial.coeff_X, Polynomial.coeff_one]

theorem hyperbolic_reverse {p : ℝ[X]} (hp : Hyperbolic p) (h0 : p.coeff 0 ≠ 0) :
    Hyperbolic p.reverse := by
  classical
  have hp0 : p ≠ 0 := fun h => h0 (by rw [h]; simp)
  have hsplits : p.Splits := Polynomial.splits_iff_card_roots.mpr hp
  have hrne : ∀ r ∈ p.roots, r ≠ 0 := by
    intro r hr hr0
    have hev : p.eval r = 0 := (Polynomial.mem_roots hp0).mp hr
    rw [hr0, ← Polynomial.coeff_zero_eq_eval_zero] at hev
    exact h0 hev
  have hfact : p = C p.leadingCoeff * (p.roots.map (fun x => X - C x)).prod :=
    hsplits.eq_prod_roots
  have hrevprod : ((p.roots.map (fun x => X - C x)).prod).reverse
      = (p.roots.map (fun x => (1 : ℝ[X]) - C x * X)).prod := by
    have := Multiset.prod_hom (p.roots.map (fun x => X - C x)) reverseMonoidHom
    simp only [reverseMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk, Multiset.map_map,
      Function.comp] at this ⊢
    rw [← this]
    congr 1
    exact Multiset.map_congr rfl fun x _ => reverse_X_sub_C x
  have hfac2 : ∀ x ∈ p.roots, (1 : ℝ[X]) - C x * X = C (-x) * (X - C x⁻¹) := by
    intro x hx
    have hx0 : x ≠ 0 := hrne x hx
    have hxx : (-x) * x⁻¹ = -1 := by field_simp
    rw [mul_sub, ← Polynomial.C_mul, hxx]
    simp
    ring
  have hCprod : (p.roots.map (fun x => (C (-x) : ℝ[X]))).prod
      = C ((p.roots.map (fun x => -x)).prod) := by
    rw [map_multiset_prod (Polynomial.C : ℝ →+* ℝ[X]) (p.roots.map (fun x => -x)),
      Multiset.map_map]
    rfl
  have hrevp : p.reverse = C (p.leadingCoeff * (p.roots.map (fun x => -x)).prod)
      * (p.roots.map (fun x => X - C x⁻¹)).prod := by
    conv_lhs => rw [hfact]
    rw [Polynomial.reverse_mul_of_domain, Polynomial.reverse_C, hrevprod,
      Multiset.map_congr rfl hfac2, Multiset.prod_map_mul, hCprod, Polynomial.C_mul]
    ring
  have hlc : p.leadingCoeff * (p.roots.map (fun x => -x)).prod ≠ 0 := by
    refine mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp0) ?_
    refine Multiset.prod_ne_zero ?_
    intro hmem
    obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.mp hmem
    exact hrne x hx (by linarith [neg_eq_zero.mp hx0])
  have hroots : p.reverse.roots = p.roots.map (fun x => x⁻¹) := by
    rw [hrevp, Polynomial.roots_C_mul _ hlc]
    have hmm : (p.roots.map (fun x => X - C x⁻¹))
        = (p.roots.map (fun x => x⁻¹)).map (fun a => X - C a) := by
      rw [Multiset.map_map]
      rfl
    rw [hmm, Polynomial.roots_multiset_prod_X_sub_C]
  unfold Hyperbolic
  rw [hroots, Multiset.card_map, natDegree_reverse_eq h0]
  exact hp

/-! ### The Newton-normalised coefficients -/

theorem natDegree_derivative_eq_sub_one {p : ℝ[X]} (hp : 1 ≤ p.natDegree) :
    (derivative p).natDegree = p.natDegree - 1 := by
  refine le_antisymm (Polynomial.natDegree_derivative_le p) (Polynomial.le_natDegree_of_ne_zero ?_)
  have hd : p.natDegree - 1 + 1 = p.natDegree := by omega
  rw [Polynomial.coeff_derivative, hd]
  have hp0 : p ≠ 0 := fun h => by rw [h] at hp; simp at hp
  refine mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp0) ?_
  have hcast : ((p.natDegree - 1 : ℕ) : ℝ) + 1 = (p.natDegree : ℝ) := by
    rw [Nat.cast_sub hp]
    push_cast
    ring
  rw [hcast]
  exact_mod_cast Nat.one_le_iff_ne_zero.mp hp

/-- The Newton-normalised coefficient `A_k = c_{d-k} / C(d,k)`. -/
noncomputable def newtonCoeff (p : ℝ[X]) (k : ℕ) : ℝ :=
  p.coeff (p.natDegree - k) / (p.natDegree.choose k : ℝ)

theorem choose_sub_mul {d k : ℕ} (hk : k + 1 ≤ d) :
    (d - k) * d.choose k = d * (d - 1).choose k := by
  have h1 : (d - 1 + 1) * (d - 1).choose k = (d - 1 + 1).choose (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq (d - 1) k
  have hd1 : d - 1 + 1 = d := by omega
  rw [hd1] at h1
  have h2 : d.choose (k + 1) * (k + 1) = d.choose k * (d - k) := Nat.choose_succ_right_eq d k
  rw [mul_comm, ← h2, ← h1]

theorem newtonCoeff_derivative {p : ℝ[X]} (hp : 1 ≤ p.natDegree) {k : ℕ}
    (hk : k + 1 ≤ p.natDegree) :
    newtonCoeff (derivative p) k = (p.natDegree : ℝ) * newtonCoeff p k := by
  have hdd : (derivative p).natDegree = p.natDegree - 1 := natDegree_derivative_eq_sub_one hp
  have hidx : p.natDegree - 1 - k + 1 = p.natDegree - k := by omega
  rw [newtonCoeff, newtonCoeff, hdd, Polynomial.coeff_derivative, hidx]
  have hcast : ((p.natDegree - 1 - k : ℕ) : ℝ) + 1 = ((p.natDegree - k : ℕ) : ℝ) := by
    have hstep : (p.natDegree - k : ℕ) = (p.natDegree - 1 - k) + 1 := by omega
    rw [hstep]
    push_cast
    ring
  rw [hcast]
  have hbin := choose_sub_mul (d := p.natDegree) (k := k) hk
  have hbinR : ((p.natDegree - k : ℕ) : ℝ) * (p.natDegree.choose k : ℝ)
      = (p.natDegree : ℝ) * ((p.natDegree - 1).choose k : ℝ) := by exact_mod_cast hbin
  have hc1 : (0 : ℝ) < ((p.natDegree - 1).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hc2 : (0 : ℝ) < (p.natDegree.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  field_simp
  linear_combination (p.coeff (p.natDegree - k)) * hbinR

theorem newtonCoeff_reverse {p : ℝ[X]} (h0 : p.coeff 0 ≠ 0) {k : ℕ} (hk : k ≤ p.natDegree) :
    newtonCoeff p.reverse k = newtonCoeff p (p.natDegree - k) := by
  have hd := natDegree_reverse_eq h0
  rw [newtonCoeff, newtonCoeff, hd, Polynomial.coeff_reverse, Polynomial.revAt_le (by omega)]
  have h1 : p.natDegree - (p.natDegree - k) = k := by omega
  rw [h1, Nat.choose_symm hk]

/-! ### Newton's inequalities -/

theorem newton_quadratic {p : ℝ[X]} (hp : Hyperbolic p) (hd : p.natDegree = 2) :
    newtonCoeff p 0 * newtonCoeff p 2 ≤ (newtonCoeff p 1) ^ 2 := by
  have hp0 : p ≠ 0 := fun h => by rw [h] at hd; simp at hd
  have hcard : Multiset.card p.roots = 2 := by rw [hp, hd]
  have hne : p.roots ≠ 0 := by
    intro h
    rw [h] at hcard
    simp at hcard
  obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hne
  have hroot : p.eval r = 0 := (Polynomial.mem_roots hp0).mp hr
  have hexp : p.coeff 2 * r ^ 2 + p.coeff 1 * r + p.coeff 0 = 0 := by
    have hpeq : p = Polynomial.C (p.coeff 2) * X ^ 2 + Polynomial.C (p.coeff 1) * X
        + Polynomial.C (p.coeff 0) := by
      ext n
      match n with
      | 0 => simp
      | 1 => simp
      | 2 => simp
      | (j + 3) =>
          have : p.coeff (j + 3) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          simp [this]
    have heval : p.eval r = p.coeff 2 * r ^ 2 + p.coeff 1 * r + p.coeff 0 := by
      conv_lhs => rw [hpeq]
      simp
    rw [heval] at hroot
    exact hroot
  have hlead : p.coeff 2 ≠ 0 := by
    have := Polynomial.leadingCoeff_ne_zero.mpr hp0
    rwa [Polynomial.leadingCoeff, hd] at this
  have hdisc : 0 ≤ (p.coeff 1) ^ 2 - 4 * p.coeff 2 * p.coeff 0 := by
    have hid : (p.coeff 1) ^ 2 - 4 * p.coeff 2 * p.coeff 0
        = (p.coeff 1 + 2 * p.coeff 2 * r) ^ 2
          - 4 * p.coeff 2 * (p.coeff 2 * r ^ 2 + p.coeff 1 * r + p.coeff 0) := by ring
    rw [hid, hexp, mul_zero, sub_zero]
    exact sq_nonneg _
  rw [newtonCoeff, newtonCoeff, newtonCoeff, hd]
  norm_num
  nlinarith [hdisc]

/-- **Newton's inequalities.**  The normalised coefficients `A_k = c_{d-k}/C(d,k)` of a real-rooted
real polynomial of degree `d` are log-concave: `A_{k-1}·A_{k+1} ≤ A_k²`. -/
theorem newton_inequality : ∀ (d : ℕ) (p : ℝ[X]), Hyperbolic p → p.natDegree = d →
    ∀ k, 1 ≤ k → k + 1 ≤ d →
      newtonCoeff p (k - 1) * newtonCoeff p (k + 1) ≤ (newtonCoeff p k) ^ 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have hlow : ∀ q : ℝ[X], Hyperbolic q → q.natDegree = d → ∀ k, 1 ≤ k → k + 2 ≤ d →
        newtonCoeff q (k - 1) * newtonCoeff q (k + 1) ≤ (newtonCoeff q k) ^ 2 := by
      intro q hq hqd k hk hkd
      have hq1 : 1 ≤ q.natDegree := by omega
      have hderdeg : (derivative q).natDegree = d - 1 := by
        rw [natDegree_derivative_eq_sub_one hq1, hqd]
      have hIH := ih (d - 1) (by omega) (derivative q) (hyperbolic_derivative hq) hderdeg
        k hk (by omega)
      have e1 : newtonCoeff (derivative q) (k - 1) = (q.natDegree : ℝ) * newtonCoeff q (k - 1) :=
        newtonCoeff_derivative hq1 (by omega)
      have e2 : newtonCoeff (derivative q) k = (q.natDegree : ℝ) * newtonCoeff q k :=
        newtonCoeff_derivative hq1 (by omega)
      have e3 : newtonCoeff (derivative q) (k + 1) = (q.natDegree : ℝ) * newtonCoeff q (k + 1) :=
        newtonCoeff_derivative hq1 (by omega)
      rw [e1, e2, e3] at hIH
      have hDpos : (0 : ℝ) < (q.natDegree : ℝ) := by exact_mod_cast hq1
      have hL : (q.natDegree : ℝ) ^ 2 * (newtonCoeff q (k - 1) * newtonCoeff q (k + 1))
          = ((q.natDegree : ℝ) * newtonCoeff q (k - 1))
            * ((q.natDegree : ℝ) * newtonCoeff q (k + 1)) := by ring
      have hR : (q.natDegree : ℝ) ^ 2 * (newtonCoeff q k) ^ 2
          = ((q.natDegree : ℝ) * newtonCoeff q k) ^ 2 := by ring
      have key : (q.natDegree : ℝ) ^ 2 * (newtonCoeff q (k - 1) * newtonCoeff q (k + 1))
          ≤ (q.natDegree : ℝ) ^ 2 * (newtonCoeff q k) ^ 2 := by
        rw [hL, hR]; exact hIH
      exact le_of_mul_le_mul_left key (pow_pos hDpos 2)
    intro p hp hpd k hk hkd
    rcases le_or_gt (k + 2) d with hk2 | hk2
    · exact hlow p hp hpd k hk hk2
    · have hkd1 : k = d - 1 := by omega
      have hd2 : 2 ≤ d := by omega
      rcases eq_or_lt_of_le hd2 with hd2' | hd3
      · have hk1 : k = 1 := by omega
        subst hk1
        simpa using newton_quadratic hp (by rw [hpd, ← hd2'])
      · by_cases h0 : p.coeff 0 = 0
        · have hA : newtonCoeff p (k + 1) = 0 := by
            rw [newtonCoeff, hpd]
            have hz : d - (k + 1) = 0 := by omega
            rw [hz, h0, zero_div]
          rw [hA, mul_zero]
          positivity
        · have hrev := hyperbolic_reverse hp h0
          have hrevd : p.reverse.natDegree = d := by rw [natDegree_reverse_eq h0, hpd]
          have hone := hlow p.reverse hrev hrevd 1 le_rfl (by omega)
          have t0 : newtonCoeff p.reverse 0 = newtonCoeff p d := by
            rw [newtonCoeff_reverse h0 (by omega), hpd, Nat.sub_zero]
          have t1 : newtonCoeff p.reverse 1 = newtonCoeff p (d - 1) := by
            rw [newtonCoeff_reverse h0 (by omega), hpd]
          have t2 : newtonCoeff p.reverse 2 = newtonCoeff p (d - 2) := by
            rw [newtonCoeff_reverse h0 (by omega), hpd]
          norm_num [t0, t1, t2] at hone
          have hkm : k - 1 = d - 2 := by omega
          have hkp : k + 1 = d := by omega
          rw [hkm, hkp, hkd1, mul_comm]
          exact hone

end GaloisForLFunctions.SignAlternation
