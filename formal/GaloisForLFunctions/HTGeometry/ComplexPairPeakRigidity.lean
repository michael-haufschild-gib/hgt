import GaloisForLFunctions.HTGeometry.ComplexPairArcCriterion

/-!
# The peak dichotomy for a complex conjugate pair

Two facts about the comparison `R(t) ≥ 2 e^{β t} cos (γ t)` for a positive exponential sum `R`.

* **Rigidity.**  Contact at two points where the cosine equals `1` forces `R(t) = 2 e^{β t}`: one
  exponential, matching the conjugate pair exactly.  So the contact set on the peak lattice is
  either a single point or the whole lattice — no intermediate configuration exists.  The mechanism
  is that `e^{-β t} R(t)` is convex with a vanishing derivative at each contact, hence has vanishing
  second derivative on the segment between them, and a positive combination of exponentials has
  vanishing second derivative only when every exponent is `β`.

* **Failure of sign-change counting.**  The extremal function `2 e^{β t}(1 - cos γ t)`, which is the
  three-term sum with exponents `β` and `β ± iγ`, is nonnegative and vanishes at every point of the
  peak lattice.  So it admits zero configurations of every length, whereas a three-term sum with
  *real* exponents has at most two zeros counted with multiplicity.  No Descartes-type bound
  survives the passage to complex exponents.
-/

open Set Real

namespace GaloisForLFunctions.HTGeometry

variable {m : ℕ}

/-! ## Rigidity -/

private theorem sin_eq_zero_of_cos_eq_one {x : ℝ} (h : Real.cos x = 1) : Real.sin x = 0 := by
  have := Real.sin_sq_add_cos_sq x
  rw [h] at this
  have hsq : Real.sin x ^ (2 : ℕ) = 0 := by linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

private theorem contact_deriv_eq_zero (c a : Fin m → ℝ) {β γ p : ℝ}
    (hcp : Real.cos (γ * p) = 1)
    (hdom : ∀ t : ℝ, 2 * Real.cos (γ * t) ≤ expSum c (fun i => a i - β) t)
    (hp : expSum c (fun i => a i - β) p = 2) :
    expSum (fun i => c i * (a i - β)) (fun i => a i - β) p = 0 := by
  set b : Fin m → ℝ := fun i => a i - β with hb
  have hgderiv : ∀ t : ℝ, HasDerivAt (fun s => expSum c b s - 2 * Real.cos (γ * s))
      (expSum (fun i => c i * b i) b t + 2 * γ * Real.sin (γ * t)) t := by
    intro t
    have h1 := hasDerivAt_expSum c b t
    have hin : HasDerivAt (fun s : ℝ => γ * s) γ t := by
      simpa using (hasDerivAt_id t).const_mul γ
    have h2 : HasDerivAt (fun s : ℝ => 2 * Real.cos (γ * s)) (2 * (-Real.sin (γ * t) * γ)) t :=
      (hin.cos).const_mul 2
    refine (h1.sub h2).congr_deriv ?_
    ring
  have hmin : IsMinOn (fun s => expSum c b s - 2 * Real.cos (γ * s)) univ p := by
    intro t _
    have h1 := hdom t
    show expSum c b p - 2 * Real.cos (γ * p) ≤ expSum c b t - 2 * Real.cos (γ * t)
    rw [hp, hcp]
    linarith
  have hlocal : IsLocalMin (fun s => expSum c b s - 2 * Real.cos (γ * s)) p :=
    hmin.isLocalMin (isOpen_univ.mem_nhds (mem_univ p))
  have hzero := hlocal.hasDerivAt_eq_zero (hgderiv p)
  rw [sin_eq_zero_of_cos_eq_one hcp] at hzero
  linarith

private theorem rigidity_aux (c a : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    {β γ p q : ℝ} (hpq : p < q)
    (hcp : Real.cos (γ * p) = 1) (hcq : Real.cos (γ * q) = 1)
    (hdom : ∀ t : ℝ, 2 * Real.cos (γ * t) ≤ expSum c (fun i => a i - β) t)
    (hp : expSum c (fun i => a i - β) p = 2) (hq : expSum c (fun i => a i - β) q = 2) :
    ∀ i, a i = β := by
  set b : Fin m → ℝ := fun i => a i - β with hb
  -- the first derivative vanishes at both contacts
  have hdp : expSum (fun i => c i * b i) b p = 0 := contact_deriv_eq_zero c a hcp hdom hp
  have hdq : expSum (fun i => c i * b i) b q = 0 := contact_deriv_eq_zero c a hcq hdom hq
  -- the first derivative is monotone, hence identically zero between them
  have hd1 : deriv (expSum c b) = expSum (fun i => c i * b i) b := deriv_expSum c b
  have hd2 : deriv (expSum (fun i => c i * b i) b)
      = expSum (fun i => c i * b i * b i) b := deriv_expSum _ b
  have hmono : Monotone (expSum (fun i => c i * b i) b) := by
    refine monotone_of_deriv_nonneg
      ((contDiff_expSum _ b).differentiable (by simp)) (fun t => ?_)
    rw [hd2, expSum]
    refine Finset.sum_nonneg (fun i _ => ?_)
    have hrw : c i * b i * b i = c i * b i ^ (2 : ℕ) := by ring
    rw [hrw]
    exact mul_nonneg (mul_nonneg (hc i).le (sq_nonneg _)) (Real.exp_pos _).le
  have hzeroOn : ∀ t ∈ Icc p q, expSum (fun i => c i * b i) b t = 0 := by
    intro t ht
    have h1 : expSum (fun i => c i * b i) b p ≤ expSum (fun i => c i * b i) b t := hmono ht.1
    have h2 : expSum (fun i => c i * b i) b t ≤ expSum (fun i => c i * b i) b q := hmono ht.2
    rw [hdp] at h1
    rw [hdq] at h2
    linarith
  -- so the second derivative vanishes at an interior point
  have hmid : (p + q) / 2 ∈ Ioo p q := ⟨by linarith, by linarith⟩
  have hev : expSum (fun i => c i * b i) b =ᶠ[nhds ((p + q) / 2)] (fun _ => (0 : ℝ)) := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hmid) (fun t ht => ?_)
    exact hzeroOn t (Ioo_subset_Icc_self ht)
  have hsecond : expSum (fun i => c i * b i * b i) b ((p + q) / 2) = 0 := by
    rw [← hd2, hev.deriv_eq]
    simp
  -- a positive combination of exponentials vanishes only if every coefficient does
  rw [expSum] at hsecond
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => by
    have hrw : c i * b i * b i = c i * b i ^ (2 : ℕ) := by ring
    rw [hrw]
    exact mul_nonneg (mul_nonneg (hc i).le (sq_nonneg _)) (Real.exp_pos _).le)).mp hsecond
  intro i
  have hi := hterm i (Finset.mem_univ i)
  have hexp : Real.exp (b i * ((p + q) / 2)) ≠ 0 := Real.exp_ne_zero _
  have hcb : c i * b i * b i = 0 := by
    rcases mul_eq_zero.mp hi with h | h
    · exact h
    · exact absurd h hexp
  have hbi : b i = 0 := by
    rcases mul_eq_zero.mp hcb with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (ne_of_gt (hc i))
      · exact h'
    · exact h
  have : a i - β = 0 := hbi
  linarith

/-- **Peak rigidity.**  A positive exponential sum that dominates `2 e^{β t} cos (γ t)` everywhere
and touches it at two distinct points of the peak lattice is the single exponential `2 e^{β t}`. -/
theorem eq_two_mul_exp_of_two_contacts (c a : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    {β γ p q : ℝ} (hpq : p ≠ q)
    (hcp : Real.cos (γ * p) = 1) (hcq : Real.cos (γ * q) = 1)
    (hdom : ∀ t : ℝ, 2 * Real.exp (β * t) * Real.cos (γ * t) ≤ expSum c a t)
    (hp : expSum c a p = 2 * Real.exp (β * p))
    (hq : expSum c a q = 2 * Real.exp (β * q)) :
    ∀ t : ℝ, expSum c a t = 2 * Real.exp (β * t) := by
  have hshift : ∀ t : ℝ, expSum c (fun i => a i - β) t = Real.exp (-(β * t)) * expSum c a t :=
    fun t => expSum_shift_apply c a β t
  have hdomS : ∀ t : ℝ, 2 * Real.cos (γ * t) ≤ expSum c (fun i => a i - β) t := by
    intro t
    rw [hshift t]
    have hpos : (0 : ℝ) < Real.exp (-(β * t)) := Real.exp_pos _
    have hd := hdom t
    have hid : Real.exp (-(β * t)) * (2 * Real.exp (β * t) * Real.cos (γ * t))
        = 2 * Real.cos (γ * t) := by
      rw [show Real.exp (-(β * t)) * (2 * Real.exp (β * t) * Real.cos (γ * t))
          = 2 * (Real.exp (-(β * t)) * Real.exp (β * t)) * Real.cos (γ * t) by ring,
        ← Real.exp_add]
      simp
    calc 2 * Real.cos (γ * t)
        = Real.exp (-(β * t)) * (2 * Real.exp (β * t) * Real.cos (γ * t)) := hid.symm
      _ ≤ Real.exp (-(β * t)) * expSum c a t := mul_le_mul_of_nonneg_left hd hpos.le
  have hcontact : ∀ r : ℝ, expSum c a r = 2 * Real.exp (β * r) →
      expSum c (fun i => a i - β) r = 2 := by
    intro r hr
    rw [hshift r, hr,
      show Real.exp (-(β * r)) * (2 * Real.exp (β * r))
        = 2 * (Real.exp (-(β * r)) * Real.exp (β * r)) by ring, ← Real.exp_add]
    simp
  have hall : ∀ i, a i = β := by
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact rigidity_aux c a hc hlt hcp hcq hdomS (hcontact p hp) (hcontact q hq)
    · exact rigidity_aux c a hc hgt hcq hcp hdomS (hcontact q hq) (hcontact p hp)
  -- every exponent is `β`, so the sum is a single exponential of total mass `2`
  have hsum : ∑ i, c i = 2 := by
    have := hcontact p hp
    rw [expSum] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hall i]
    simp
  intro t
  rw [expSum]
  have : ∀ i : Fin m, c i * Real.exp (a i * t) = c i * Real.exp (β * t) := by
    intro i; rw [hall i]
  rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.sum_mul, hsum]

/-! ## Failure of sign-change counting -/

private theorem vanishesTo_le_one {f : ℝ → ℝ} {n : ℕ} {x : ℝ} (hn : n ≤ 1) (h : f x = 0) :
    VanishesTo f n x := by
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  rwa [iteratedDeriv_zero]

/-- **Sign-change counting fails once the exponents are complex.**  The three-term sum
`2 e^{β t} - e^{(β+iγ)t} - e^{(β-iγ)t} = 2 e^{β t}(1 - cos γ t)` admits zero configurations of every
length, while `laguerre_zeroList_length_le` bounds those of a three-term sum with real exponents by
two. -/
theorem exists_zeroList_length_eq_of_complex_pair {β γ : ℝ} (hγ : 0 < γ) (N : ℕ) :
    ∃ l : List ℝ,
      IsZeroList (fun t => 2 * Real.exp (β * t) * (1 - Real.cos (γ * t))) l ∧ l.length = N := by
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  set w : ℝ := 2 * π / γ with hw
  have hwpos : (0 : ℝ) < w := by rw [hw]; positivity
  set f : Fin N → ℝ := fun i => (i : ℕ) * w with hf
  have hmono : ∀ ⦃i j : Fin N⦄, i < j → f i ≤ f j := by
    intro i j hij
    have h1 : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by
      exact_mod_cast le_of_lt (Fin.lt_def.mp hij)
    exact mul_le_mul_of_nonneg_right h1 hwpos.le
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 : ((i : ℕ) : ℝ) * w = ((j : ℕ) : ℝ) * w := hij
    have h2 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := mul_right_cancel₀ (ne_of_gt hwpos) h1
    exact Fin.ext (by exact_mod_cast h2)
  have hzero : ∀ i : Fin N, 2 * Real.exp (β * f i) * (1 - Real.cos (γ * f i)) = 0 := by
    intro i
    have harg : γ * f i = ((i : ℕ) : ℝ) * (2 * π) := by
      rw [hf, hw]
      field_simp
    rw [harg, Real.cos_nat_mul_two_pi]
    ring
  refine ⟨List.ofFn f, ⟨List.pairwise_ofFn.mpr hmono, ?_⟩, by simp⟩
  intro x
  by_cases hx : x ∈ List.ofFn f
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
    refine vanishesTo_le_one ?_ ?_
    · exact List.nodup_iff_count_le_one.mp (List.nodup_ofFn.mpr hinj) x
    · rw [← hi]; exact hzero i
  · rw [List.count_eq_zero.mpr hx]
    exact vanishesTo_zero _ _


/-! ## The criterion on the peak lattice -/

/-- **The peak-lattice criterion.**  Around the `k`-th peak `2πk/γ` the arc criterion reads directly
in terms of `cos (γ t)`: the sum dominates `2 e^{β t} cos (γ t)` on the whole arc where the cosine is
nonnegative exactly when one exponential lying under `R` reaches the Legendre profile `Φ(ν/γ)` of the
cap at the peak.  Only the value at the peak enters — no count of zeros or sign changes. -/
theorem cos_peak_arc_le_iff (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i)
    {β γ : ℝ} (hγ : 0 < γ) (k : ℤ) :
    (∀ t ∈ Icc ((k : ℝ) * (2 * π) / γ - π / (2 * γ)) ((k : ℝ) * (2 * π) / γ + π / (2 * γ)),
        2 * Real.exp (β * t) * Real.cos (γ * t) ≤ expSum c a t)
      ↔ ∃ ν L : ℝ, (∀ t : ℝ, Real.exp (L + (β + ν) * t) ≤ expSum c a t)
          ∧ capProfile (ν / γ) ≤ L + ν * ((k : ℝ) * (2 * π) / γ) := by
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hcos : ∀ t : ℝ, Real.cos (γ * (t - (k : ℝ) * (2 * π) / γ)) = Real.cos (γ * t) := by
    intro t
    have harg : γ * (t - (k : ℝ) * (2 * π) / γ) = γ * t - (k : ℝ) * (2 * π) := by
      field_simp
    rw [harg, Real.cos_sub_int_mul_two_pi]
  have hiff := cos_arc_le_iff_exists_separating c a hm hc (β := β) (γ := γ)
    (p := (k : ℝ) * (2 * π) / γ) hγ
  constructor
  · intro h
    refine hiff.mp (fun t ht => ?_)
    rw [hcos t]
    exact h t ht
  · intro h t ht
    have := hiff.mpr h t ht
    rwa [hcos t] at this

end GaloisForLFunctions.HTGeometry
