import GaloisForLFunctions.HTGeometry.NewtonInequalities

/-!
# The Turán ratio has a universal Newton floor

For any real family `x_1, …, x_N` the elementary symmetric functions satisfy Newton's inequalities in
normalised form, `(e_n/C(N,n))² ≥ (e_{n-1}/C(N,n-1))(e_{n+1}/C(N,n+1))`.  Clearing the binomials
with the identity `C(N,n)²·n·(N−n) = C(N,n−1)·C(N,n+1)·(n+1)·(N−n+1)` gives the **universal floor**

`(n+1)·e_{n-1}e_{n+1} ≤ n·e_n²`,

i.e. `g_n = e_n²/(e_{n-1}e_{n+1}) ≥ (n+1)/n` whenever the atoms are positive.  The floor is uniform
in `N`, so it survives the limit `N → ∞` of an infinite positive divisor atom sequence.

The consequence recorded on the `pa9-turan-newton-floor` card is that a unit of the observed `1/n`
decay in `g_n − 1` is forced by Newton/binomial geometry before any source-specific positivity
appears: the source-specific margin is the de-biased residual `g_n/((n+1)/n) − 1`.

## Main results

* `newton_esymm` — Newton's inequalities for elementary symmetric functions;
* `newton_floor_finite` — the cleared floor `(n+1)e_{n-1}e_{n+1} ≤ n e_n²`, for **any** real family;
* `turan_ratio_newton_floor` — `g_n ≥ (n+1)/n` for positive atoms;
* `newton_floor_limit` — the floor survives the infinite-atom limit.
-/

namespace GaloisForLFunctions

open Polynomial Finset

/-- The `j`-th elementary symmetric function of a finite family of reals. -/
noncomputable def esymmFin {N : ℕ} (x : Fin N → ℝ) (j : ℕ) : ℝ :=
  ∑ t ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∏ i ∈ t, x i

/-- `∏_i (X + x_i)`, the generating polynomial of the elementary symmetric functions. -/
noncomputable def prodLinear {N : ℕ} (x : Fin N → ℝ) : ℝ[X] :=
  ∏ i : Fin N, (X + Polynomial.C (x i))

theorem natDegree_prodLinear {N : ℕ} (x : Fin N → ℝ) : (prodLinear x).natDegree = N := by
  rw [prodLinear, Polynomial.natDegree_prod _ _ (fun i _ => Polynomial.X_add_C_ne_zero (x i))]
  simp

theorem hyperbolic_prodLinear {N : ℕ} (x : Fin N → ℝ) :
    SignAlternation.Hyperbolic (prodLinear x) := by
  have heq : prodLinear x
      = (((Finset.univ : Finset (Fin N)).val.map (fun i => -x i)).map
          (fun a => X - Polynomial.C a)).prod := by
    rw [prodLinear, Finset.prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
    simp only [Function.comp_apply, map_neg, sub_neg_eq_add]
  unfold SignAlternation.Hyperbolic
  rw [natDegree_prodLinear]
  conv_lhs => rw [heq]
  rw [Polynomial.roots_multiset_prod_X_sub_C]
  simp

theorem newtonCoeff_prodLinear {N : ℕ} (x : Fin N → ℝ) {j : ℕ} (hj : j ≤ N) :
    SignAlternation.newtonCoeff (prodLinear x) j = esymmFin x j / (N.choose j : ℝ) := by
  rw [SignAlternation.newtonCoeff, natDegree_prodLinear]
  congr 1
  rw [prodLinear, Finset.prod_X_add_C_coeff _ _ (by simp)]
  rw [esymmFin]
  congr 2
  simp
  omega

/-- **Newton's inequalities for elementary symmetric functions.**  For any finite family of reals,
the sequence `e_j / C(N,j)` is log-concave. -/
theorem newton_esymm {N : ℕ} (x : Fin N → ℝ) {n : ℕ} (hn : 1 ≤ n) (hnN : n + 1 ≤ N) :
    (esymmFin x (n - 1) / (N.choose (n - 1) : ℝ)) * (esymmFin x (n + 1) / (N.choose (n + 1) : ℝ))
      ≤ (esymmFin x n / (N.choose n : ℝ)) ^ (2 : ℕ) := by
  have h := SignAlternation.newton_inequality N (prodLinear x) (hyperbolic_prodLinear x)
    (natDegree_prodLinear x) n hn hnN
  rwa [newtonCoeff_prodLinear x (by omega), newtonCoeff_prodLinear x (by omega),
    newtonCoeff_prodLinear x (by omega)] at h

theorem choose_turan_identity {N n : ℕ} (hn : 1 ≤ n) (hnN : n + 1 ≤ N) :
    (N.choose n) ^ (2 : ℕ) * n * (N - n) = (N.choose (n - 1)) * (N.choose (n + 1)) * (n + 1) * (N - n + 1) := by
  have h1 : N.choose (n + 1) * (n + 1) = N.choose n * (N - n) := Nat.choose_succ_right_eq N n
  have h2 : N.choose (n - 1 + 1) * (n - 1 + 1) = N.choose (n - 1) * (N - (n - 1)) :=
    Nat.choose_succ_right_eq N (n - 1)
  have hn1 : n - 1 + 1 = n := by omega
  have hn2 : N - (n - 1) = N - n + 1 := by omega
  rw [hn1, hn2] at h2
  calc (N.choose n) ^ (2 : ℕ) * n * (N - n)
      = (N.choose n * n) * (N.choose n * (N - n)) := by ring
    _ = (N.choose (n - 1) * (N - n + 1)) * (N.choose (n + 1) * (n + 1)) := by rw [h2, h1]
    _ = (N.choose (n - 1)) * (N.choose (n + 1)) * (n + 1) * (N - n + 1) := by ring

/-- **The universal Newton floor, finite form.**  `(n+1)·e_{n-1}e_{n+1} ≤ n·e_n²` for every finite
family of reals — the cleared form of `g_n ≥ (n+1)/n`. -/
theorem newton_floor_finite {N : ℕ} (x : Fin N → ℝ) {n : ℕ} (hn : 1 ≤ n) (hnN : n + 1 ≤ N) :
    ((n : ℝ) + 1) * (esymmFin x (n - 1) * esymmFin x (n + 1)) ≤ (n : ℝ) * (esymmFin x n) ^ (2 : ℕ) := by
  have hc0 : (0 : ℝ) < (N.choose (n - 1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hc1 : (0 : ℝ) < (N.choose n : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hc2 : (0 : ℝ) < (N.choose (n + 1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have h := newton_esymm x hn hnN
  rw [div_mul_div_comm, div_pow, div_le_div_iff₀ (by positivity) (by positivity)] at h
  -- h : e_{n-1} e_{n+1} * C(N,n)^(2 : ℕ) ≤ e_n^(2 : ℕ) * (C(N,n-1) * C(N,n+1))
  have hid : ((N.choose n : ℝ)) ^ (2 : ℕ) * (n : ℝ) * ((N - n : ℕ) : ℝ)
      = (N.choose (n - 1) : ℝ) * (N.choose (n + 1) : ℝ) * ((n : ℝ) + 1) * (((N - n : ℕ) : ℝ) + 1) := by
    have := choose_turan_identity hn hnN
    have hcast : (((N.choose n) ^ (2 : ℕ) * n * (N - n) : ℕ) : ℝ)
        = (((N.choose (n - 1)) * (N.choose (n + 1)) * (n + 1) * (N - n + 1) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
    push_cast at hcast
    linarith [hcast]
  have hsq : (0 : ℝ) ≤ (esymmFin x n) ^ (2 : ℕ) := sq_nonneg _
  have hNn : (0 : ℝ) ≤ ((N - n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hν0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  set E := esymmFin x (n - 1) * esymmFin x (n + 1) with hE
  set F := (esymmFin x n) ^ (2 : ℕ) with hF
  set A := ((N.choose n : ℝ)) ^ (2 : ℕ) with hA'
  set B := (N.choose (n - 1) : ℝ) * (N.choose (n + 1) : ℝ) with hB'
  set ν := (n : ℝ) with hν
  set m := ((N - n : ℕ) : ℝ) with hm
  have hA : 0 < A := by rw [hA']; positivity
  have hνm : (0 : ℝ) < (ν + 1) * (m + 1) := by
    have : (0:ℝ) < ν + 1 := by linarith
    have h2 : (0:ℝ) < m + 1 := by linarith
    positivity
  have step3 : E * A * ((ν + 1) * (m + 1)) ≤ F * (A * ν * m) := by
    have step1 : E * A * ((ν + 1) * (m + 1)) ≤ F * B * ((ν + 1) * (m + 1)) :=
      mul_le_mul_of_nonneg_right h (le_of_lt hνm)
    have step2 : F * B * ((ν + 1) * (m + 1)) = F * (A * ν * m) := by rw [hid]; ring
    rw [← step2]
    exact step1
  have step4 : A * ((ν + 1) * (m + 1) * E) ≤ A * (ν * m * F) := by
    calc A * ((ν + 1) * (m + 1) * E) = E * A * ((ν + 1) * (m + 1)) := by ring
      _ ≤ F * (A * ν * m) := step3
      _ = A * (ν * m * F) := by ring
  have step5 : (ν + 1) * (m + 1) * E ≤ ν * m * F := le_of_mul_le_mul_left step4 hA
  have hmF : ν * m * F ≤ ν * (m + 1) * F := by nlinarith [mul_nonneg hν0 hsq]
  have step6 : (m + 1) * ((ν + 1) * E) ≤ (m + 1) * (ν * F) := by
    calc (m + 1) * ((ν + 1) * E) = (ν + 1) * (m + 1) * E := by ring
      _ ≤ ν * m * F := step5
      _ ≤ ν * (m + 1) * F := hmF
      _ = (m + 1) * (ν * F) := by ring
  exact le_of_mul_le_mul_left step6 (by linarith)

theorem esymmFin_pos {N : ℕ} {x : Fin N → ℝ} (hx : ∀ i, 0 < x i) {j : ℕ} (hj : j ≤ N) :
    0 < esymmFin x j := by
  rw [esymmFin]
  refine Finset.sum_pos (fun t _ => Finset.prod_pos fun i _ => hx i) ?_
  refine Finset.powersetCard_nonempty.mpr ?_
  simpa using hj

/-- **The universal Newton floor for the Turán ratio.**  For strictly positive atoms the Turán
ratio `g_n = e_n² / (e_{n-1} e_{n+1})` is at least `(n+1)/n`. -/
theorem turan_ratio_newton_floor {N : ℕ} {x : Fin N → ℝ} (hx : ∀ i, 0 < x i) {n : ℕ}
    (hn : 1 ≤ n) (hnN : n + 1 ≤ N) :
    ((n : ℝ) + 1) / (n : ℝ)
      ≤ (esymmFin x n) ^ (2 : ℕ) / (esymmFin x (n - 1) * esymmFin x (n + 1)) := by
  have h := newton_floor_finite x hn hnN
  have hp1 : 0 < esymmFin x (n - 1) := esymmFin_pos hx (by omega)
  have hp2 : 0 < esymmFin x (n + 1) := esymmFin_pos hx (by omega)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [div_le_div_iff₀ hn0 (by positivity)]
  linarith [h]

/-- **The universal Newton floor in the limit.**  If the elementary symmetric functions of the
truncations of an infinite atom sequence converge, the limits still satisfy the floor
`(n+1)·a_{n-1}a_{n+1} ≤ n·a_n²`, i.e. `g_n ≥ (n+1)/n`. -/
theorem newton_floor_limit (y : ℕ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, Filter.Tendsto (fun N => esymmFin (fun i : Fin N => y i) j) Filter.atTop
      (nhds (a j))) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * (a (n - 1) * a (n + 1)) ≤ (n : ℝ) * (a n) ^ (2 : ℕ) := by
  have h1 : Filter.Tendsto
      (fun N => ((n : ℝ) + 1) * (esymmFin (fun i : Fin N => y i) (n - 1)
        * esymmFin (fun i : Fin N => y i) (n + 1)))
      Filter.atTop (nhds (((n : ℝ) + 1) * (a (n - 1) * a (n + 1)))) :=
    ((ha (n - 1)).mul (ha (n + 1))).const_mul _
  have h2 : Filter.Tendsto
      (fun N => (n : ℝ) * (esymmFin (fun i : Fin N => y i) n) ^ (2 : ℕ))
      Filter.atTop (nhds ((n : ℝ) * (a n) ^ (2 : ℕ))) := ((ha n).pow 2).const_mul _
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [Filter.eventually_ge_atTop (n + 1)] with N hN
  exact newton_floor_finite _ hn hN

end GaloisForLFunctions
