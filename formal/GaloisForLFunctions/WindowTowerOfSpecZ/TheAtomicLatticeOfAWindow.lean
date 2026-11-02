import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowDirichletAlgebra

/-!
# The atomic lattice of a window

Fix a level `N ≥ 1` and a profile `φ` vanishing off `[−δ, 0]` with `0 ≤ δ < log((N+1)/N)`. The
**atom** of the integer `m ≤ N` is `b_m(u) = φ(u + log N − log m)`, a copy of `φ` at the point
`log(m/N)` of the window; the atoms of distinct integers have disjoint supports.

* **The window shifts multiply the atoms** (`windowShift_atom_of_le`, `windowShift_atom_of_lt`):
  `T_{log n} b_m = b_{nm}` if `nm ≤ N`, and `0` otherwise.
* **The regular representation** (`windowRepFun_atomicEmbedding`): the atomic embedding
  `ι(g) = Σ_{m ≤ N} g(m) m^{−1/2} b_m` intertwines the window representation with multiplication in the
  truncated Dirichlet ring: `ρ_A(f) ι(g) = ι(f * g)` on a window of level `N`. The integers
  `m ≤ e^A`, as atoms, are a free module of rank one over the window algebra.
* **The metric of the lattice** (`integral_atomicEmbedding_mul`): `⟨ι(g), ι(h)⟩ = ‖φ‖² Σ_{k ≤ N} g(k)h(k)/k`.
* **Weil's arithmetic term on the lattice is multiplication by `Λ`**
  (`integral_windowRep_atomicEmbedding`): `⟨ρ_A(f)ι(g), ι(h)⟩ = ‖φ‖² Σ_{k ≤ N} (f * g)(k) h(k)/k`; for
  `f = Λ` the arithmetic part of Weil's form on atomic tests is `−2‖φ‖² Σ_k (Λ * g)(k) g(k)/k`.
* **The pole plane of the lattice** (`poleA_atomicEmbedding`, `poleB_atomicEmbedding`): the pole
  pairings of `ι(g)` are `N^{−1/2}(Σ_m g(m))·∫φe^{v/2}` and `N^{1/2}(Σ_m g(m)/m)·∫φe^{−v/2}`: the
  values at `s = 0` and `s = 1` of the window Dirichlet polynomial `Σ_{m ≤ N} g(m)m^{−s}`. Their
  product, the pole term of Weil's form, does not depend on the level.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ

/-- The atom of `m` at level `N`: `b_m(u) = φ(u + log N − log m)`, located at `log(m/N)`. -/
def atom (N : ℕ) (φ : ℝ → ℝ) (m : ℕ) : ℝ → ℝ := fun u => φ (u + Real.log N - Real.log m)

/-- The atomic embedding `ι(g) = Σ_{1 ≤ m ≤ N} g(m) m^{−1/2} b_m`. -/
def atomicEmbedding (N : ℕ) (φ : ℝ → ℝ) (g : ArithmeticFunction ℝ) : ℝ → ℝ := fun u =>
  ∑ m ∈ Finset.Icc 1 N, g m / Real.sqrt m * atom N φ m u

variable {N : ℕ} {φ : ℝ → ℝ} {δ : ℝ}

/-- An admissible profile at level `N`: supported in `[−δ, 0]`, narrower than `log((N+1)/N)`. -/
structure IsAtomProfile (N : ℕ) (δ : ℝ) (φ : ℝ → ℝ) : Prop where
  nonneg : 0 ≤ δ
  narrow : δ < Real.log (N + 1) - Real.log N
  vanish : ∀ v, v ∉ Icc (-δ) 0 → φ v = 0

theorem log_sub_log_pos {N : ℕ} (hN : 1 ≤ N) : 0 < Real.log (N + 1) - Real.log N := by
  have h0 : (0 : ℝ) < N := by exact_mod_cast hN
  have := Real.log_lt_log h0 (by linarith : (N : ℝ) < N + 1)
  linarith

/-- Distinct integers `k < m ≤ N` are farther apart on the log scale than the atom width. -/
theorem lt_log_sub_log (hφ : IsAtomProfile N δ φ) {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m)
    (hmN : m ≤ N) : δ < Real.log m - Real.log k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast (hkm.le.trans hmN)
  have hkm' : (k : ℝ) + 1 ≤ m := by exact_mod_cast hkm
  have hN0 : (0 : ℝ) < N := by linarith
  -- `log((k+1)/k) ≥ log((N+1)/N)` since `x ↦ log(x+1) − log x` decreases
  have hmono : Real.log (N + 1) - Real.log N ≤ Real.log (k + 1) - Real.log k := by
    rw [← Real.log_div (by linarith) hN0.ne', ← Real.log_div (by linarith) hk0.ne']
    refine Real.log_le_log (div_pos (by linarith) hN0) ?_
    rw [div_le_div_iff₀ hN0 hk0]
    nlinarith
  have hstep : Real.log (k + 1) ≤ Real.log m := Real.log_le_log (by linarith) hkm'
  linarith [hφ.narrow]

/-- Atoms of an integer `m ≤ N` live in `[log(m/N) − δ, log(m/N)]`. -/
theorem atom_eq_zero_of_not_mem (hφ : IsAtomProfile N δ φ) (m : ℕ) {u : ℝ}
    (hu : u + Real.log N - Real.log m ∉ Icc (-δ) 0) : atom N φ m u = 0 := hφ.vanish _ hu

/-- **The window shift multiplies atoms**: `T_{log n} b_m = b_{nm}` for `nm ≤ N`. -/
theorem windowShift_atom_of_le (hφ : IsAtomProfile N δ φ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hnm : n * m ≤ N) : windowShift (Real.log n) (atom N φ m) = atom N φ (n * m) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log (n * m : ℕ) = Real.log n + Real.log m := by
    rw [Nat.cast_mul, Real.log_mul hn0.ne' hm0.ne']
  have hle : Real.log (n * m : ℕ) ≤ Real.log N :=
    Real.log_le_log (by positivity) (by exact_mod_cast hnm)
  funext u
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le _ hu, atom, atom, hlog]; ring_nf
  · rw [windowShift_apply_of_pos _ hu, atom, hφ.vanish]
    intro h; linarith [h.2]

/-- **Products beyond the level leave the window**: `T_{log n} b_m = 0` for `nm > N`. -/
theorem windowShift_atom_of_lt (hφ : IsAtomProfile N δ φ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hnm : N < n * m) : windowShift (Real.log n) (atom N φ m) = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hN1 : Real.log (N + 1) ≤ Real.log n + Real.log m := by
    rw [← Real.log_mul hn0.ne' hm0.ne']
    exact Real.log_le_log (by positivity) (by exact_mod_cast hnm)
  funext u
  rcases le_or_gt u 0 with hu | hu
  · rw [windowShift_apply_of_le _ hu, atom, hφ.vanish]
    · rfl
    · intro h; linarith [h.1, hφ.narrow]
  · rw [windowShift_apply_of_pos _ hu]; rfl

/-! ### The regular representation -/

theorem windowShift_atomicEmbedding (t : ℝ) (g : ArithmeticFunction ℝ) (u : ℝ) :
    windowShift t (atomicEmbedding N φ g) u =
      ∑ m ∈ Finset.Icc 1 N, g m / Real.sqrt m * windowShift t (atom N φ m) u :=
  windowShift_sum _ t (fun m => g m / Real.sqrt m) (fun m => atom N φ m) u

/-- **The atoms carry the regular representation of the window algebra**:
`ρ_A(f) ι(g) = ι(f * g)` on a window of level `N`. -/
theorem windowRepFun_atomicEmbedding {A : ℝ} (hA : windowLevel A = N) (hφ : IsAtomProfile N δ φ)
    (f g : ArithmeticFunction ℝ) :
    windowRepFun A f (atomicEmbedding N φ g) = atomicEmbedding N φ (f * g) := by
  funext u
  set G : ℕ × ℕ → ℝ := fun x => f x.1 * g x.2 / Real.sqrt (x.1 * x.2 : ℕ) *
    atom N φ (x.1 * x.2) u with hG
  have hlhs : windowRepFun A f (atomicEmbedding N φ g) u =
      ∑ x ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun x => x.1 * x.2 ≤ N), G x := by
    rw [Finset.sum_filter, Finset.sum_product, windowRepFun, hA]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [windowShift_atomicEmbedding, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have ha1 := (Finset.mem_Icc.mp ha).1
    have hb1 := (Finset.mem_Icc.mp hb).1
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    split_ifs with hab
    · rw [windowShift_atom_of_le hφ ha1 hb1 hab, hG]
      simp only
      rw [Nat.cast_mul, Real.sqrt_mul (by linarith)]
      field_simp
    · rw [windowShift_atom_of_lt hφ ha1 hb1 (not_le.mp hab), Pi.zero_apply, mul_zero, mul_zero]
  have hrhs : atomicEmbedding N φ (f * g) u =
      ∑ k ∈ Finset.Icc 1 N, ∑ x ∈ k.divisorsAntidiagonal, G x := by
    rw [atomicEmbedding]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ArithmeticFunction.mul_apply, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hG, (Nat.mem_divisorsAntidiagonal.mp hx).1]
  rw [hlhs, hrhs, sum_Icc_divisorsAntidiagonal]

/-! ### The metric of the lattice -/

theorem integral_atom_mul_atom (hφ : IsAtomProfile N δ φ) {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hkN : k ≤ N) (hmN : m ≤ N) :
    ∫ u, atom N φ k u * atom N φ m u = if k = m then ∫ v, φ v ^ 2 else 0 := by
  split_ifs with hkm
  · subst hkm
    have e : (fun u => atom N φ k u * atom N φ k u) =
        fun u => (fun v => φ v ^ 2) (u + (Real.log N - Real.log k)) :=
      funext fun u => by simp only [atom, add_sub_assoc, sq]
    rw [e, integral_add_right_eq_self (fun v => φ v ^ 2)]
  · -- disjoint supports
    have hdisj : ∀ {a b : ℕ}, 1 ≤ a → a < b → b ≤ N → ∀ u,
        atom N φ a u * atom N φ b u = 0 := fun {a b} ha hab hbN u => by
      have hsep := lt_log_sub_log hφ ha hab hbN
      by_cases h1 : u + Real.log N - Real.log a ∈ Icc (-δ) 0
      · rw [atom_eq_zero_of_not_mem hφ b fun h2 => by linarith [h1.2, h2.1, hsep], mul_zero]
      · rw [atom_eq_zero_of_not_mem hφ a h1, zero_mul]
    have hz : (fun u => atom N φ k u * atom N φ m u) = fun _ => 0 := by
      funext u
      rcases lt_or_gt_of_ne hkm with h | h
      · exact hdisj hk h hmN u
      · rw [mul_comm]; exact hdisj hm h hkN u
    rw [hz, integral_zero]

theorem continuous_atom (hc : Continuous φ) (m : ℕ) : Continuous (atom N φ m) := by
  unfold atom; fun_prop

theorem hasCompactSupport_atom (hφ : IsAtomProfile N δ φ) (m : ℕ) :
    HasCompactSupport (atom N φ m) := by
  have hcs : HasCompactSupport φ := HasCompactSupport.intro (isCompact_Icc (a := -δ) (b := 0))
    hφ.vanish
  have e : atom N φ m = fun u => φ (u + (Real.log N - Real.log m)) :=
    funext fun u => by simp only [atom, add_sub_assoc]
  rw [e]
  exact RHTower.WeilMarkovPole.hasCompactSupport_comp_add hcs _

theorem integrable_atom_mul (hφ : IsAtomProfile N δ φ) (hc : Continuous φ) (k m : ℕ) :
    Integrable fun u => atom N φ k u * atom N φ m u :=
  ((continuous_atom hc k).mul (continuous_atom hc m)).integrable_of_hasCompactSupport
    (hasCompactSupport_atom hφ k).mul_right

/-- `⟨ι(g), ι(h)⟩ = ‖φ‖² Σ_{k ≤ N} g(k)h(k)/k`. -/
theorem integral_atomicEmbedding_mul (hφ : IsAtomProfile N δ φ) (hc : Continuous φ)
    (g h : ArithmeticFunction ℝ) :
    ∫ u, atomicEmbedding N φ g u * atomicEmbedding N φ h u =
      (∫ v, φ v ^ 2) * ∑ k ∈ Finset.Icc 1 N, g k * h k / k := by
  have hexp : ∀ u, atomicEmbedding N φ g u * atomicEmbedding N φ h u =
      ∑ k ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (g k / Real.sqrt k * (h m / Real.sqrt m)) * (atom N φ k u * atom N φ m u) := fun u => by
    rw [atomicEmbedding, atomicEmbedding, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun m _ =>
    (integrable_atom_mul hφ hc k m).const_mul _]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ fun m _ => (integrable_atom_mul hφ hc k m).const_mul _]
  have hk1 := (Finset.mem_Icc.mp hk).1
  rw [Finset.sum_eq_single_of_mem k hk fun m hm hmk => by
    rw [integral_const_mul, integral_atom_mul_atom hφ hk1 (Finset.mem_Icc.mp hm).1
      (Finset.mem_Icc.mp hk).2 (Finset.mem_Icc.mp hm).2, if_neg (Ne.symm hmk), mul_zero]]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hs : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
  rw [integral_const_mul, integral_atom_mul_atom hφ hk1 hk1 (Finset.mem_Icc.mp hk).2
    (Finset.mem_Icc.mp hk).2, if_pos rfl, div_mul_div_comm, hs]
  ring

/-- **Weil's arithmetic term on the atomic lattice is multiplication in the window algebra**:
`⟨ρ_A(f)ι(g), ι(h)⟩ = ‖φ‖² Σ_{k ≤ N} (f * g)(k) h(k)/k`. -/
theorem integral_windowRep_atomicEmbedding {A : ℝ} (hA : windowLevel A = N)
    (hφ : IsAtomProfile N δ φ) (hc : Continuous φ) (f g h : ArithmeticFunction ℝ) :
    ∫ u, windowRepFun A f (atomicEmbedding N φ g) u * atomicEmbedding N φ h u =
      (∫ v, φ v ^ 2) * ∑ k ∈ Finset.Icc 1 N, (f * g) k * h k / k := by
  rw [windowRepFun_atomicEmbedding hA hφ, integral_atomicEmbedding_mul hφ hc]

/-! ### The pole plane of the lattice -/

theorem integral_atom_mul_exp (m : ℕ) (c : ℝ) : ∫ u, atom N φ m u * Real.exp (c * u) =
      Real.exp (c * (Real.log m - Real.log N)) * ∫ v, φ v * Real.exp (c * v) := by
  rw [← integral_const_mul,
    ← integral_add_right_eq_self (fun u => atom N φ m u * Real.exp (c * u))
      (Real.log m - Real.log N)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [atom]
  rw [show v + (Real.log m - Real.log N) + Real.log N - Real.log m = v by ring,
    show c * (v + (Real.log m - Real.log N)) = c * (Real.log m - Real.log N) + c * v by ring,
    Real.exp_add]
  ring

theorem integrable_atom_mul_exp (hφ : IsAtomProfile N δ φ) (hc : Continuous φ) (m : ℕ) (c : ℝ) :
    Integrable fun u => atom N φ m u * Real.exp (c * u) :=
  ((continuous_atom hc m).mul (by fun_prop)).integrable_of_hasCompactSupport
    (hasCompactSupport_atom hφ m).mul_right

theorem exp_log_div_two {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]; ring_nf

/-- The `e^{cu}`-moment of an atomic test: `Σ_m g(m) m^{−1/2} (m/N)^c ∫φe^{cv}`. -/
theorem integral_atomicEmbedding_mul_exp (hφ : IsAtomProfile N δ φ) (hc : Continuous φ)
    (g : ArithmeticFunction ℝ) (c : ℝ) :
    ∫ u, atomicEmbedding N φ g u * Real.exp (c * u) =
      (∑ m ∈ Finset.Icc 1 N, g m / Real.sqrt m * Real.exp (c * (Real.log m - Real.log N))) *
        ∫ v, φ v * Real.exp (c * v) := by
  simp_rw [atomicEmbedding, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ fun m _ => (integrable_atom_mul_exp hφ hc m c).const_mul _]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_const_mul, integral_atom_mul_exp]

/-- **The `s = 0` pole pairing reads `Σ_m g(m)`**: `∫ι(g)e^{u/2} = N^{−1/2}(Σ g(m))∫φe^{v/2}`. -/
theorem poleA_atomicEmbedding (hφ : IsAtomProfile N δ φ) (hc : Continuous φ) (hN : 1 ≤ N)
    (g : ArithmeticFunction ℝ) :
    ∫ u, atomicEmbedding N φ g u * Real.exp (u / 2) =
      (Real.sqrt N)⁻¹ * (∑ m ∈ Finset.Icc 1 N, g m) * ∫ v, φ v * Real.exp (v / 2) := by
  have h := integral_atomicEmbedding_mul_exp hφ hc g (1 / 2)
  simp only [show ∀ x : ℝ, 1 / 2 * x = x / 2 from fun x => by ring] at h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∑ m ∈ Finset.Icc 1 N, g m / Real.sqrt m * Real.exp ((Real.log m - Real.log N) / 2) =
      (Real.sqrt N)⁻¹ * ∑ m ∈ Finset.Icc 1 N, g m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    rw [sub_div, Real.exp_sub, exp_log_div_two hm0, exp_log_div_two hN0]
    have : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
    have : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
    field_simp
  rw [h, hsum]

/-- **The `s = 1` pole pairing reads `Σ_m g(m)/m`**: `∫ι(g)e^{−u/2} = N^{1/2}(Σ g(m)/m)∫φe^{−v/2}`. -/
theorem poleB_atomicEmbedding (hφ : IsAtomProfile N δ φ) (hc : Continuous φ) (hN : 1 ≤ N)
    (g : ArithmeticFunction ℝ) :
    ∫ u, atomicEmbedding N φ g u * Real.exp (-u / 2) =
      Real.sqrt N * (∑ m ∈ Finset.Icc 1 N, g m / m) * ∫ v, φ v * Real.exp (-v / 2) := by
  have h := integral_atomicEmbedding_mul_exp hφ hc g (-(1 / 2))
  simp only [show ∀ x : ℝ, -(1 / 2) * x = -x / 2 from fun x => by ring] at h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∑ m ∈ Finset.Icc 1 N, g m / Real.sqrt m * Real.exp (-(Real.log m - Real.log N) / 2) =
      Real.sqrt N * ∑ m ∈ Finset.Icc 1 N, g m / m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    rw [show -(Real.log m - Real.log N) / 2 = Real.log N / 2 - Real.log m / 2 by ring,
      Real.exp_sub, exp_log_div_two hm0, exp_log_div_two hN0]
    have hs : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
    have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
    rw [div_mul_div_comm, mul_div_assoc, hsq]
    field_simp
  rw [h, hsum]

end GaloisForLFunctions.WindowTowerOfSpecZ
