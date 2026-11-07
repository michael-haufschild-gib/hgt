import GaloisForLFunctions.RigidArithmeticOfCuts.TheFakePrimeMeasureIsUnique
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheExtremalFakePrimeMeasure

/-!
# Fake prime measures are profinitely rigid

At bounded level a fake prime measure has no pointwise meaning: translating an atom by a common period of the alphabet keeps every
moment. So nothing can pin the mass at a given integer. What survives is its image on residue classes.

**Rigidity.** For every modulus `k` and every class `ι ≢ 0`, and every `η > 0`, all fake prime measures of high enough level put mass
within `η` of the pronic mass of the class: `|u(ι mod k) − Σ_{r ≡ ι} 1/(r (r + 1))| ≤ η`.

The proof folds a measure of level `i!` onto `[1, i!)`, where it keeps all moments at divisors of `i!`. The folded measures are tight
for an elementary reason. If `r` is at least `N!` then `r mod m!` jumps at some `m ≥ N`, and a jump at `m` makes `r mod (m+1)!` at least
`m!`, which the moment `log (m+1)!` makes expensive. Hence no mass escapes to infinity. A limit along an ultrafilter is a fake prime
measure of every level, and this is the pronic measure.

**Every shape is reached.** On a fixed finite set `S` of positive integers, the extremal mass tends at most to the pronic mass of `S` as `K → ∞`. By strong
duality there are integer stencils with nonnegative multiplicity, at least `m` on `S`, of slope at most `m` times that mass, up to `η`. In particular
every window `[1, B)` is reached, at rate tending to `0`, and there is a spike at every integer.

So the fake prime measure closest to the true one differs from it only archimedeanly: on residues it is the truth, and its
freedom lies in where along a class the mass is placed.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The pronic measure on `r = j + 1`. -/
def pronicMeasure (j : ℕ) : ℝ := 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))

theorem pronicMeasure_nonneg (j : ℕ) : 0 ≤ pronicMeasure j := by
  rw [pronicMeasure]
  positivity

/-- The mass of the class `a` modulo `q`. -/
def classMass (u : ℕ → ℝ) (q a : ℕ) : ℝ := ∑' j, if (j + 1) % q = a then u j else 0

variable {K : ℕ} {u : ℕ → ℝ}

theorem IsFakePrimeMeasure.mono {K' : ℕ} (hu : IsFakePrimeMeasure K u) (h : K' ≤ K) :
    IsFakePrimeMeasure K' u :=
  ⟨hu.nonneg, fun k hk => hu.moment k (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans h⟩)⟩

/-- A class off zero is summable. -/
theorem IsFakePrimeMeasure.summable_class (hu : IsFakePrimeMeasure K u) {q a : ℕ} (hq : q ∈ Icc 1 K)
    (ha : 1 ≤ a) : Summable fun j => if (j + 1) % q = a then u j else 0 := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (hu.moment q hq).summable
  · split_ifs
    · exact hu.nonneg j
    · exact le_rfl
  · split_ifs with h
    · rw [h]
      have hR : (1 : ℝ) ≤ a := by exact_mod_cast ha
      exact le_mul_of_one_le_right (hu.nonneg j) hR
    · exact mul_nonneg (hu.nonneg j) (Nat.cast_nonneg _)

theorem IsFakePrimeMeasure.classMass_nonneg (hu : IsFakePrimeMeasure K u) (q a : ℕ) :
    0 ≤ classMass u q a :=
  tsum_nonneg fun j => by
    split_ifs
    · exact hu.nonneg j
    · exact le_rfl

/-- **Folding.** A function of the residue modulo `q`, vanishing at `0`, is integrated through the class masses. -/
theorem IsFakePrimeMeasure.hasSum_fold (hu : IsFakePrimeMeasure K u) {q : ℕ} (hq : q ∈ Icc 1 K)
    (φ : ℕ → ℝ) (hφ : φ 0 = 0) :
    HasSum (fun j => u j * φ ((j + 1) % q)) (∑ a ∈ Ico 1 q, classMass u q a * φ a) := by
  have hq0 : 0 < q := (mem_Icc.mp hq).1
  have hfun : (fun j => u j * φ ((j + 1) % q)) =
      fun j => ∑ a ∈ Ico 1 q, (if (j + 1) % q = a then u j else 0) * φ a := by
    funext j
    rcases Nat.eq_zero_or_pos ((j + 1) % q) with h0 | hpos
    · rw [h0, hφ, mul_zero]
      refine (sum_eq_zero fun a ha => ?_).symm
      have : (0 : ℕ) ≠ a := by
        have := (mem_Ico.mp ha).1
        omega
      simp [this]
    · have hmem : (j + 1) % q ∈ Ico 1 q := mem_Ico.mpr ⟨hpos, Nat.mod_lt _ hq0⟩
      rw [sum_eq_single_of_mem _ hmem fun a _ hne => by
        rw [if_neg hne.symm, zero_mul], if_pos rfl]
  rw [hfun]
  refine hasSum_sum fun a ha => ?_
  exact ((hu.summable_class hq (mem_Ico.mp ha).1).hasSum).mul_right (φ a)

/-- The measure folded onto `[1, q)`. -/
def foldMeasure (u : ℕ → ℝ) (q j : ℕ) : ℝ := if j + 1 < q then classMass u q (j + 1) else 0

theorem IsFakePrimeMeasure.foldMeasure_nonneg (hu : IsFakePrimeMeasure K u) (q j : ℕ) :
    0 ≤ foldMeasure u q j := by
  rw [foldMeasure]
  split_ifs
  · exact hu.classMass_nonneg _ _
  · exact le_rfl

/-- The sum over classes is the sum over the folded measure. -/
private lemma sum_Ico_eq_sum_fold (u : ℕ → ℝ) {q : ℕ} (hq : 1 ≤ q) (φ : ℕ → ℝ) :
    ∑ a ∈ Ico 1 q, classMass u q a * φ a = ∑ j ∈ range (q - 1), foldMeasure u q j * φ (j + 1) := by
  rw [sum_Ico_eq_sum_range]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  rw [foldMeasure, if_pos (by omega), add_comm 1 j]

/-- The folded measure integrates a function of the residue exactly like the measure. -/
theorem IsFakePrimeMeasure.sum_fold_eq_tsum (hu : IsFakePrimeMeasure K u) {q : ℕ} (hq : q ∈ Icc 1 K)
    (φ : ℕ → ℝ) (hφ : φ 0 = 0) :
    HasSum (fun j => u j * φ ((j + 1) % q)) (∑ j ∈ range (q - 1), foldMeasure u q j * φ (j + 1)) := by
  rw [← sum_Ico_eq_sum_fold u (mem_Icc.mp hq).1]
  exact hu.hasSum_fold hq φ hφ

/-- **The folded measure keeps the moments at the divisors of `q`.** -/
theorem IsFakePrimeMeasure.sum_fold_moment (hu : IsFakePrimeMeasure K u) {q k : ℕ} (hq : q ∈ Icc 1 K)
    (hk : k ∣ q) :
    ∑ j ∈ range (q - 1), foldMeasure u q j * (((j + 1) % k : ℕ) : ℝ) = Real.log k := by
  have hq' := mem_Icc.mp hq
  have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hk hq'.1
  have hkK : k ∈ Icc 1 K := mem_Icc.mpr ⟨hk0, (Nat.le_of_dvd hq'.1 hk).trans hq'.2⟩
  have h := hu.sum_fold_eq_tsum hq (fun a => ((a % k : ℕ) : ℝ)) (by simp)
  have hfun : (fun j => u j * ((((j + 1) % q) % k : ℕ) : ℝ)) = fun j => u j * (((j + 1) % k : ℕ) : ℝ) := by
    funext j
    rw [Nat.mod_mod_of_dvd _ hk]
  simp only [hfun] at h
  exact h.unique (hu.moment k hkK)

/-- A jump: past `N!`, the residue modulo `m!` must change at some `m ≥ N`. -/
private lemma exists_jump {N i r : ℕ} (hNi : N ≤ i) (h1 : N.factorial ≤ r) (h2 : r < i.factorial) :
    ∃ m ∈ Ico N i, m.factorial ≤ r % (m + 1).factorial := by
  by_contra hall
  push Not at hall
  have hstep : ∀ n, N ≤ n → n ≤ i → r % n.factorial = r % N.factorial := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro _; rfl
    | succ n hn ih =>
      intro hni
      have hlt := hall n (mem_Ico.mpr ⟨hn, by omega⟩)
      have hdvd : n.factorial ∣ (n + 1).factorial := Nat.factorial_dvd_factorial (by omega)
      have hmm : (r % (n + 1).factorial) % n.factorial = r % n.factorial := Nat.mod_mod_of_dvd _ hdvd
      rw [Nat.mod_eq_of_lt hlt] at hmm
      rw [hmm, ih (by omega)]
  have hi := hstep i hNi le_rfl
  rw [Nat.mod_eq_of_lt h2] at hi
  have := Nat.mod_lt r (Nat.factorial_pos N)
  omega

/-- The tail bound for one jump. -/
private lemma pow_mul_le_factorial (m : ℕ) : (m + 1) ^ 2 * 2 ^ m ≤ 24 * m.factorial := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.factorial_succ]
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m <;> norm_num [Nat.factorial]
    · have hkey : 2 * (m + 1 + 1) ^ 2 ≤ (m + 1) ^ 3 := by
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
        ring_nf
        nlinarith
      calc (m + 1 + 1) ^ 2 * 2 ^ (m + 1) = 2 * (m + 1 + 1) ^ 2 * 2 ^ m := by ring
        _ ≤ (m + 1) ^ 3 * 2 ^ m := Nat.mul_le_mul_right _ hkey
        _ = (m + 1) * ((m + 1) ^ 2 * 2 ^ m) := by ring
        _ ≤ (m + 1) * (24 * m.factorial) := Nat.mul_le_mul_left _ ih
        _ = 24 * ((m + 1) * m.factorial) := by ring

/-- `log (m+1)! / m! ≤ 24 (1/2)^m`. -/
private lemma log_factorial_div_le (m : ℕ) :
    Real.log ((m + 1).factorial : ℝ) / (m.factorial : ℝ) ≤ 24 * (1 / 2 : ℝ) ^ m := by
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hlog : Real.log ((m + 1).factorial : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
    have hle : (((m + 1).factorial : ℕ) : ℝ) ≤ ((m : ℝ) + 1) ^ (m + 1) := by
      have := Nat.factorial_le_pow (m + 1)
      exact_mod_cast this
    have hpos : (0 : ℝ) < ((m + 1).factorial : ℕ) := by exact_mod_cast Nat.factorial_pos _
    have h1 := Real.log_le_log hpos hle
    rw [Real.log_pow] at h1
    have h2 : Real.log ((m : ℝ) + 1) ≤ (m : ℝ) + 1 := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (m : ℝ) + 1)
      linarith
    push_cast at h1
    calc _ ≤ ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1) := h1
      _ ≤ ((m : ℝ) + 1) * ((m : ℝ) + 1) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = _ := by ring
  have hkey : ((m : ℝ) + 1) ^ 2 * 2 ^ m ≤ 24 * m.factorial := by
    exact_mod_cast pow_mul_le_factorial m
  rw [div_le_iff₀ hfac]
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hval : (24 : ℝ) * (1 / 2 : ℝ) ^ m * m.factorial = 24 * m.factorial / 2 ^ m := by
    rw [one_div, inv_pow]
    field_simp
  rw [hval, le_div_iff₀ h2m]
  calc Real.log ((m + 1).factorial : ℝ) * 2 ^ m ≤ ((m : ℝ) + 1) ^ 2 * 2 ^ m :=
        mul_le_mul_of_nonneg_right hlog h2m.le
    _ ≤ _ := hkey

/-- The tolerance of the tail at scale `N!`. -/
def foldTail (N : ℕ) : ℝ := 48 * (1 / 2 : ℝ) ^ N

theorem tendsto_foldTail : Tendsto foldTail atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul 48
  rw [mul_zero] at h
  exact h

private lemma sum_Ico_geom {N i : ℕ} (h : N ≤ i) :
    ∑ m ∈ Ico N i, (24 : ℝ) * (1 / 2 : ℝ) ^ m = 48 * ((1 / 2 : ℝ) ^ N - (1 / 2 : ℝ) ^ i) := by
  induction i, h using Nat.le_induction with
  | base => simp
  | succ i hi ih =>
    rw [sum_Ico_succ_top hi, ih, pow_succ]
    ring

/-- **Tightness.** A fake prime measure folded at level `i!` has mass at most `foldTail N` beyond `N!`. -/
theorem IsFakePrimeMeasure.sum_fold_tail_le {i N : ℕ} (hu : IsFakePrimeMeasure i.factorial u) (hNi : N ≤ i) :
    ∑ j ∈ Ico (N.factorial - 1) (i.factorial - 1), foldMeasure u i.factorial j ≤ foldTail N := by
  have hq : i.factorial ∈ Icc 1 i.factorial := mem_Icc.mpr ⟨Nat.factorial_pos i, le_rfl⟩
  have hpoint : ∀ j ∈ Ico (N.factorial - 1) (i.factorial - 1), foldMeasure u i.factorial j ≤
      ∑ m ∈ Ico N i, foldMeasure u i.factorial j * (((j + 1) % (m + 1).factorial : ℕ) : ℝ) /
        (m.factorial : ℝ) := by
    intro j hj
    obtain ⟨h1, h2⟩ := mem_Ico.mp hj
    have hN0 := Nat.factorial_pos N
    obtain ⟨m, hm, hle⟩ := exists_jump (r := j + 1) hNi (by omega) (by omega)
    have hv := hu.foldMeasure_nonneg i.factorial j
    have hterm : ∀ m' ∈ Ico N i, 0 ≤ foldMeasure u i.factorial j *
        (((j + 1) % (m' + 1).factorial : ℕ) : ℝ) / (m'.factorial : ℝ) := fun m' _ => by positivity
    refine le_trans ?_ (single_le_sum hterm hm)
    have hmfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    rw [le_div_iff₀ hmfac]
    have hleR : (m.factorial : ℝ) ≤ (((j + 1) % (m + 1).factorial : ℕ) : ℝ) := by exact_mod_cast hle
    exact mul_le_mul_of_nonneg_left hleR hv
  have hsub : Ico (N.factorial - 1) (i.factorial - 1) ⊆ range (i.factorial - 1) := by
    intro x hx
    exact mem_range.mpr (mem_Ico.mp hx).2
  have hnn : ∀ j ∈ range (i.factorial - 1), 0 ≤ ∑ m ∈ Ico N i,
      foldMeasure u i.factorial j * (((j + 1) % (m + 1).factorial : ℕ) : ℝ) / (m.factorial : ℝ) :=
    fun j _ => sum_nonneg fun m _ => by
      have hv := hu.foldMeasure_nonneg i.factorial j
      positivity
  calc _ ≤ ∑ j ∈ Ico (N.factorial - 1) (i.factorial - 1), ∑ m ∈ Ico N i,
        foldMeasure u i.factorial j * (((j + 1) % (m + 1).factorial : ℕ) : ℝ) / (m.factorial : ℝ) :=
        sum_le_sum hpoint
    _ ≤ ∑ j ∈ range (i.factorial - 1), ∑ m ∈ Ico N i,
        foldMeasure u i.factorial j * (((j + 1) % (m + 1).factorial : ℕ) : ℝ) / (m.factorial : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun j hj _ => hnn j hj
    _ = ∑ m ∈ Ico N i, Real.log ((m + 1).factorial : ℝ) / (m.factorial : ℝ) := by
        rw [sum_comm]
        refine sum_congr rfl fun m hm => ?_
        have hdvd : (m + 1).factorial ∣ i.factorial :=
          Nat.factorial_dvd_factorial (by have := (mem_Ico.mp hm).2; omega)
        rw [← hu.sum_fold_moment hq hdvd, sum_div]
    _ ≤ ∑ m ∈ Ico N i, (24 : ℝ) * (1 / 2 : ℝ) ^ m := sum_le_sum fun m _ => log_factorial_div_le m
    _ = 48 * ((1 / 2 : ℝ) ^ N - (1 / 2 : ℝ) ^ i) := sum_Ico_geom hNi
    _ ≤ foldTail N := by
        have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ i := by positivity
        rw [foldTail]
        linarith

/-- A single value of the folded measure is bounded by a fixed moment. -/
private lemma IsFakePrimeMeasure.foldMeasure_le {i j : ℕ} (hu : IsFakePrimeMeasure i.factorial u)
    (hj : j + 2 ≤ i) : foldMeasure u i.factorial j ≤ Real.log ((j + 2).factorial : ℝ) := by
  have hq : i.factorial ∈ Icc 1 i.factorial := mem_Icc.mpr ⟨Nat.factorial_pos i, le_rfl⟩
  have hdvd : (j + 2).factorial ∣ i.factorial := Nat.factorial_dvd_factorial hj
  have hmom := hu.sum_fold_moment hq hdvd
  have hlt : j + 1 < (j + 2).factorial := by
    have h1 := Nat.self_le_factorial (j + 2)
    have h2 : j + 2 ≤ (j + 2).factorial := h1
    omega
  have hle : (j + 2).factorial ≤ i.factorial := Nat.factorial_le hj
  have hmem : j ∈ range (i.factorial - 1) := mem_range.mpr (by omega)
  rw [← hmom]
  have hterm : ∀ x ∈ range (i.factorial - 1), 0 ≤ foldMeasure u i.factorial x *
      (((x + 1) % (j + 2).factorial : ℕ) : ℝ) := fun x _ =>
    mul_nonneg (hu.foldMeasure_nonneg _ _) (Nat.cast_nonneg _)
  refine le_trans ?_ (single_le_sum hterm hmem)
  rw [Nat.mod_eq_of_lt hlt]
  have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j + 1)
  exact le_mul_of_one_le_right (hu.foldMeasure_nonneg _ _) h1

/-- A bounded sequence has a limit along an ultrafilter. -/
private lemma exists_tendsto_hyperfilter (f : ℕ → ℝ) {C : ℝ}
    (h : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), f i ∈ Set.Icc 0 C) :
    ∃ x ∈ Set.Icc 0 C, Tendsto f (hyperfilter ℕ : Filter ℕ) (𝓝 x) := by
  obtain ⟨x, hx, hle⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := C)).ultrafilter_le_nhds
    (Ultrafilter.map f (hyperfilter ℕ)) (by
      rw [Ultrafilter.coe_map, le_principal_iff, Filter.mem_map]
      exact h)
  rw [Ultrafilter.coe_map] at hle
  exact ⟨x, hx, hle⟩

private lemma eventually_ge_hyperfilter (n : ℕ) : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), n ≤ i := by
  have h := (eventually_ge_atTop n)
  rw [← Nat.cofinite_eq_atTop] at h
  exact hyperfilter_le_cofinite h

/-- **The limit of folded measures is the pronic measure.** -/
theorem tendsto_foldMeasure_pronic {v : ℕ → ℕ → ℝ}
    (hv : ∀ i, IsFakePrimeMeasure i.factorial (v i)) (j : ℕ) :
    Tendsto (fun i => foldMeasure (v i) i.factorial j) (hyperfilter ℕ : Filter ℕ)
      (𝓝 (pronicMeasure j)) := by
  have hex : ∀ j, ∃ x ∈ Set.Icc (0 : ℝ) (Real.log ((j + 2).factorial : ℝ)),
      Tendsto (fun i => foldMeasure (v i) i.factorial j) (hyperfilter ℕ : Filter ℕ) (𝓝 x) := by
    intro j
    refine exists_tendsto_hyperfilter _ ?_
    filter_upwards [eventually_ge_hyperfilter (j + 2)] with i hi
    exact ⟨(hv i).foldMeasure_nonneg _ _, (hv i).foldMeasure_le hi⟩
  choose w hw hlim using hex
  have hw0 : ∀ j, 0 ≤ w j := fun j => (hw j).1
  -- The moments of the limit, truncated at `N!`.
  have htrunc : ∀ (k N : ℕ), 1 ≤ k →
      ∑ j ∈ range (N.factorial - 1), w j * (((j + 1) % k : ℕ) : ℝ) ≤ Real.log k ∧
      Real.log k ≤ ∑ j ∈ range (N.factorial - 1), w j * (((j + 1) % k : ℕ) : ℝ) +
        (k : ℝ) * foldTail N := by
    intro k N hk
    have hT : Tendsto (fun i => ∑ j ∈ range (N.factorial - 1),
        foldMeasure (v i) i.factorial j * (((j + 1) % k : ℕ) : ℝ)) (hyperfilter ℕ : Filter ℕ)
        (𝓝 (∑ j ∈ range (N.factorial - 1), w j * (((j + 1) % k : ℕ) : ℝ))) :=
      tendsto_finsetSum _ fun j _ => (hlim j).mul_const _
    have hsplit : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
        ∑ j ∈ range (N.factorial - 1), foldMeasure (v i) i.factorial j * (((j + 1) % k : ℕ) : ℝ) ≤
            Real.log k ∧
        Real.log k ≤ ∑ j ∈ range (N.factorial - 1),
          foldMeasure (v i) i.factorial j * (((j + 1) % k : ℕ) : ℝ) + (k : ℝ) * foldTail N := by
      filter_upwards [eventually_ge_hyperfilter (max k N)] with i hi
      have hik : k ≤ i := (le_max_left _ _).trans hi
      have hiN : N ≤ i := (le_max_right _ _).trans hi
      have hq : i.factorial ∈ Icc 1 i.factorial := mem_Icc.mpr ⟨Nat.factorial_pos i, le_rfl⟩
      have hmom := (hv i).sum_fold_moment hq (Nat.dvd_factorial hk hik)
      have hle : N.factorial - 1 ≤ i.factorial - 1 := Nat.sub_le_sub_right (Nat.factorial_le hiN) 1
      rw [range_eq_Ico] at hmom ⊢
      rw [← sum_Ico_consecutive _ (Nat.zero_le _) hle] at hmom
      have htail0 : 0 ≤ ∑ j ∈ Ico (N.factorial - 1) (i.factorial - 1),
          foldMeasure (v i) i.factorial j * (((j + 1) % k : ℕ) : ℝ) :=
        sum_nonneg fun j _ => mul_nonneg ((hv i).foldMeasure_nonneg _ _) (Nat.cast_nonneg _)
      have htail1 : ∑ j ∈ Ico (N.factorial - 1) (i.factorial - 1),
          foldMeasure (v i) i.factorial j * (((j + 1) % k : ℕ) : ℝ) ≤ (k : ℝ) * foldTail N := by
        have hk0 : 0 < k := hk
        calc _ ≤ ∑ j ∈ Ico (N.factorial - 1) (i.factorial - 1),
              foldMeasure (v i) i.factorial j * (k : ℝ) := by
              refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ ((hv i).foldMeasure_nonneg _ _)
              exact_mod_cast (Nat.mod_lt _ hk0).le
          _ = (k : ℝ) * ∑ j ∈ Ico (N.factorial - 1) (i.factorial - 1), foldMeasure (v i) i.factorial j := by
              rw [← sum_mul, mul_comm]
          _ ≤ _ := mul_le_mul_of_nonneg_left ((hv i).sum_fold_tail_le hiN) (Nat.cast_nonneg k)
      constructor <;> linarith
    have hne : (hyperfilter ℕ : Filter ℕ).NeBot := inferInstance
    refine ⟨le_of_tendsto hT (hsplit.mono fun i hi => hi.1), ?_⟩
    have hT' := hT.add_const ((k : ℝ) * foldTail N)
    exact ge_of_tendsto hT' (hsplit.mono fun i hi => hi.2)
  -- So the limit is a fake prime measure of every level.
  have hfake : ∀ K, IsFakePrimeMeasure K w := by
    refine fun K => ⟨hw0, fun k hk => ?_⟩
    have hk1 := (mem_Icc.mp hk).1
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hnn : ∀ j, 0 ≤ w j * (((j + 1) % k : ℕ) : ℝ) := fun j => mul_nonneg (hw0 j) (Nat.cast_nonneg _)
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
    have hmono : Monotone fun n => ∑ j ∈ range n, w j * (((j + 1) % k : ℕ) : ℝ) :=
      sum_mono_set_of_nonneg hnn |>.comp fun _ _ h => range_subset_range.mpr h
    have hub : ∀ n, ∑ j ∈ range n, w j * (((j + 1) % k : ℕ) : ℝ) ≤ Real.log k := by
      intro n
      have hn : n ≤ (n + 2).factorial - 1 := by
        have := Nat.self_le_factorial (n + 2)
        omega
      exact (hmono hn).trans (htrunc k (n + 2) hk1).1
    refine tendsto_order.mpr ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have hsmall := (tendsto_foldTail.const_mul (k : ℝ)).eventually
        (gt_mem_nhds (by rw [mul_zero]; linarith : (k : ℝ) * 0 < Real.log k - a))
      obtain ⟨N, hN⟩ := hsmall.exists
      filter_upwards [eventually_ge_atTop (N.factorial - 1)] with n hn
      have h1 := (htrunc k N hk1).2
      have h2 := hmono hn
      simp only at h2
      linarith
    · exact Eventually.of_forall fun n => lt_of_le_of_lt (hub n) hb
  have hval := RigidArithmeticOfCuts.eq_pronic_of_forall_isFakePrimeMeasure hfake j
  rw [pronicMeasure, ← hval]
  exact hlim j

/-- The pronic mass over a set of residues is summable and approached by its truncations. -/
private lemma tendsto_pronic_prefix {k ι : ℕ} (hk : 1 ≤ k) (hι : 1 ≤ ι) :
    Tendsto (fun N : ℕ => ∑ j ∈ range (N.factorial - 1),
        pronicMeasure j * (if (j + 1) % k = ι then (1 : ℝ) else 0)) atTop
      (𝓝 (classMass pronicMeasure k ι)) := by
  have hfake : IsFakePrimeMeasure k pronicMeasure := isFakePrimeMeasure_pronic k
  have hs := (hfake.summable_class (mem_Icc.mpr ⟨hk, le_rfl⟩) hι).hasSum
  have hN : Tendsto (fun N : ℕ => N.factorial - 1) atTop atTop := by
    refine tendsto_atTop_mono (f := fun N : ℕ => N - 1) (fun N => ?_) ?_
    · exact Nat.sub_le_sub_right (Nat.self_le_factorial N) 1
    · exact tendsto_sub_atTop_nat 1
  refine (hs.tendsto_sum_nat.comp hN).congr fun N => ?_
  simp only [Function.comp]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **Profinite rigidity.** For each class `ι ≢ 0` modulo `k` and each `η > 0`, every fake prime measure of high enough level gives
the class its pronic mass, within `η`. -/
theorem exists_level_classMass_close {k ι : ℕ} (hι1 : 1 ≤ ι) (hιk : ι < k) {η : ℝ} (hη : 0 < η) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → ∀ u : ℕ → ℝ, IsFakePrimeMeasure K u →
      |classMass u k ι - classMass pronicMeasure k ι| ≤ η := by
  by_contra hcon
  push Not at hcon
  have hk1 : 1 ≤ k := by omega
  choose K hK v hv hfar using fun i : ℕ => hcon i.factorial
  have hv' : ∀ i, IsFakePrimeMeasure i.factorial (v i) := fun i => (hv i).mono (hK i)
  -- The prefix at a scale where both tails are small.
  have hsmall : ∀ᶠ N : ℕ in atTop, foldTail N < η / 3 ∧
      |∑ j ∈ range (N.factorial - 1), pronicMeasure j * (if (j + 1) % k = ι then (1 : ℝ) else 0) -
        classMass pronicMeasure k ι| < η / 3 := by
    refine (tendsto_foldTail.eventually (gt_mem_nhds (by positivity))).and ?_
    have h := (tendsto_pronic_prefix hk1 hι1).sub_const (classMass pronicMeasure k ι)
    rw [sub_self] at h
    have h2 := h.abs
    rw [abs_zero] at h2
    exact h2.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN1, hN2⟩ := hsmall.exists
  have hT : Tendsto (fun i => ∑ j ∈ range (N.factorial - 1),
      foldMeasure (v i) i.factorial j * (if (j + 1) % k = ι then (1 : ℝ) else 0))
      (hyperfilter ℕ : Filter ℕ)
      (𝓝 (∑ j ∈ range (N.factorial - 1), pronicMeasure j * (if (j + 1) % k = ι then (1 : ℝ) else 0))) :=
    tendsto_finsetSum _ fun j _ => (tendsto_foldMeasure_pronic hv' j).mul_const _
  have hclose : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
      |∑ j ∈ range (N.factorial - 1),
          foldMeasure (v i) i.factorial j * (if (j + 1) % k = ι then (1 : ℝ) else 0) -
        ∑ j ∈ range (N.factorial - 1), pronicMeasure j * (if (j + 1) % k = ι then (1 : ℝ) else 0)| <
        η / 3 := by
    have h := hT.sub_const
      (∑ j ∈ range (N.factorial - 1), pronicMeasure j * (if (j + 1) % k = ι then (1 : ℝ) else 0))
    rw [sub_self] at h
    have h2 := h.abs
    rw [abs_zero] at h2
    exact h2.eventually (gt_mem_nhds (by positivity))
  obtain ⟨i, hi1, hi2⟩ := (hclose.and (eventually_ge_hyperfilter (max k N))).exists
  have hik : k ≤ i := (le_max_left _ _).trans hi2
  have hiN : N ≤ i := (le_max_right _ _).trans hi2
  have hfari := hfar i
  -- The class mass is the folded sum.
  have hq : i.factorial ∈ Icc 1 i.factorial := mem_Icc.mpr ⟨Nat.factorial_pos i, le_rfl⟩
  have hdvd : k ∣ i.factorial := Nat.dvd_factorial hk1 hik
  have hιne : (0 : ℕ) % k ≠ ι := by
    rw [Nat.zero_mod]
    omega
  have hfold := (hv' i).sum_fold_eq_tsum hq (fun a => if a % k = ι then (1 : ℝ) else 0)
    (by simp only [hιne, if_false])
  have hmass : ∑ j ∈ range (i.factorial - 1),
      foldMeasure (v i) i.factorial j * (if (j + 1) % k = ι then (1 : ℝ) else 0) = classMass (v i) k ι := by
    refine hfold.tsum_eq.symm.trans ?_
    rw [classMass]
    refine tsum_congr fun j => ?_
    rw [Nat.mod_mod_of_dvd _ hdvd]
    split_ifs <;> simp
  have hle : N.factorial - 1 ≤ i.factorial - 1 := Nat.sub_le_sub_right (Nat.factorial_le hiN) 1
  rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le _) hle, ← range_eq_Ico] at hmass
  have htail0 : 0 ≤ ∑ j ∈ Ico (N.factorial - 1) (i.factorial - 1),
      foldMeasure (v i) i.factorial j * (if (j + 1) % k = ι then (1 : ℝ) else 0) :=
    sum_nonneg fun j _ => mul_nonneg ((hv' i).foldMeasure_nonneg _ _) (by split_ifs <;> norm_num)
  have htail1 : ∑ j ∈ Ico (N.factorial - 1) (i.factorial - 1),
      foldMeasure (v i) i.factorial j * (if (j + 1) % k = ι then (1 : ℝ) else 0) ≤ foldTail N := by
    refine le_trans (sum_le_sum fun j _ => ?_) ((hv' i).sum_fold_tail_le hiN)
    refine mul_le_of_le_one_right ((hv' i).foldMeasure_nonneg _ _) ?_
    split_ifs <;> norm_num
  have habs1 := abs_lt.mp hi1
  have habs2 := abs_lt.mp hN2
  have hfin : |classMass (v i) k ι - classMass pronicMeasure k ι| ≤ η := by
    rw [abs_le]
    constructor <;> linarith
  exact absurd hfari (not_lt.mpr hfin)

/-- The pronic partial sums telescope. -/
private lemma sum_range_pronic (n : ℕ) : ∑ j ∈ range n, pronicMeasure j = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pronicMeasure]
    push_cast
    field_simp
    ring

/-- The classes of a target below `q` have pronic mass at most the pronic mass of the target, plus `1/q`. -/
private lemma sum_classMass_pronic_le {S : Finset ℕ} {q : ℕ} (hS : ∀ r ∈ S, 1 ≤ r ∧ r < q) (hq1 : 1 ≤ q) :
    ∑ a ∈ S, classMass pronicMeasure q a ≤ targetMass pronicMeasure S + 1 / (q : ℝ) := by
  classical
  have hfake : IsFakePrimeMeasure q pronicMeasure := isFakePrimeMeasure_pronic q
  have hq : q ∈ Icc 1 q := mem_Icc.mpr ⟨hq1, le_rfl⟩
  have hsum : HasSum (fun j => ∑ a ∈ S, if (j + 1) % q = a then pronicMeasure j else 0)
      (∑ a ∈ S, classMass pronicMeasure q a) :=
    hasSum_sum fun a ha => (hfake.summable_class hq (hS a ha).1).hasSum
  rw [← hsum.tsum_eq]
  refine Real.tsum_le_of_sum_range_le (fun j => sum_nonneg fun a _ => ?_) fun n => ?_
  · split_ifs
    · exact pronicMeasure_nonneg j
    · exact le_rfl
  -- A term is present only if `j + 1` lies in the target or at or above `q`.
  have hterm : ∀ j, (∑ a ∈ S, if (j + 1) % q = a then pronicMeasure j else 0) ≤
      (if j + 1 ∈ S then pronicMeasure j else 0) + (if q - 1 ≤ j then pronicMeasure j else 0) := by
    intro j
    have hp := pronicMeasure_nonneg j
    have hle : (∑ a ∈ S, if (j + 1) % q = a then pronicMeasure j else 0) ≤
        if (j + 1) % q ∈ S then pronicMeasure j else 0 := by
      split_ifs with hmem
      · rw [sum_eq_single_of_mem _ hmem fun a _ hne => by rw [if_neg hne.symm], if_pos rfl]
      · refine le_of_eq (sum_eq_zero fun a ha => ?_)
        rw [if_neg]
        rintro rfl
        exact hmem ha
    refine hle.trans ?_
    by_cases hlt : j + 1 < q
    · rw [Nat.mod_eq_of_lt hlt]
      split_ifs <;> linarith
    · have h2 : q - 1 ≤ j := by omega
      rw [if_pos h2]
      split_ifs <;> linarith
  refine (sum_le_sum fun j _ => hterm j).trans ?_
  rw [sum_add_distrib, sum_ite, sum_ite]
  simp only [sum_const_zero, add_zero]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hA : ∑ j ∈ (range n).filter (fun j => j + 1 ∈ S), pronicMeasure j ≤ targetMass pronicMeasure S := by
    have hinj : Set.InjOn (fun r : ℕ => r - 1) (S : Set ℕ) := by
      intro a ha b hb hab
      have h1 := (hS a ha).1
      have h2 := (hS b hb).1
      simp only at hab
      omega
    rw [targetMass, ← sum_image (f := pronicMeasure) hinj]
    refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => pronicMeasure_nonneg j
    exact mem_image.mpr ⟨j + 1, (mem_filter.mp hj).2, by simp⟩
  have hC : ∑ j ∈ (range n).filter (fun j => q - 1 ≤ j), pronicMeasure j ≤ 1 / (q : ℝ) := by
    by_cases hnq : q - 1 ≤ n
    · have hset : (range n).filter (fun j => q - 1 ≤ j) = Ico (q - 1) n := by
        ext j
        simp only [mem_filter, mem_range, mem_Ico]
        omega
      rw [hset, sum_Ico_eq_sub _ hnq, sum_range_pronic, sum_range_pronic]
      have e : ((q - 1 : ℕ) : ℝ) + 1 = q := by
        rw [Nat.cast_sub hq1]
        push_cast
        ring
      rw [e]
      have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · have hset : (range n).filter (fun j => q - 1 ≤ j) = ∅ := by
        ext j
        simp only [mem_filter, mem_range, notMem_empty, iff_false, not_and, not_le]
        omega
      rw [hset, sum_empty]
      positivity
  linarith

/-- **The mass of a fixed target tends to its pronic mass from above, at most.** At high level no fake prime measure puts on a finite set
more than its pronic mass, up to `η`. -/
theorem exists_level_targetMass_le {S : Finset ℕ} (hS : ∀ r ∈ S, 1 ≤ r) {η : ℝ} (hη : 0 < η) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → ∀ u : ℕ → ℝ, IsFakePrimeMeasure K u →
      targetMass u S ≤ targetMass pronicMeasure S + η := by
  classical
  -- A modulus above the target with `1/q` small.
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = max (S.sup id + 1) (⌈2 / η⌉₊ + 1) := ⟨_, rfl⟩
  have hSq : ∀ r ∈ S, 1 ≤ r ∧ r < q := fun r hr => by
    have h1 : r ≤ S.sup id := Finset.le_sup (f := id) hr
    have h2 : S.sup id + 1 ≤ q := hq ▸ le_max_left _ _
    exact ⟨hS r hr, by omega⟩
  have hq1 : 1 ≤ q := hq ▸ (Nat.le_add_left _ _).trans (le_max_left _ _)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqη : 1 / (q : ℝ) ≤ η / 2 := by
    have h1 : 2 / η ≤ (q : ℝ) := by
      have h2 : ⌈2 / η⌉₊ + 1 ≤ q := hq ▸ le_max_right _ _
      have h3 : ((⌈2 / η⌉₊ + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast h2
      have h4 := Nat.le_ceil (2 / η)
      push_cast at h3
      linarith
    rw [div_le_iff₀ hq0]
    rw [div_le_iff₀ hη] at h1
    linarith
  -- Each class is close at high level.
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℝ, ξ = η / (2 * ((S.card : ℝ) + 1)) := ⟨_, rfl⟩
  have hξ : 0 < ξ := by rw [hξdef]; positivity
  have hclose : ∀ a ∈ S, ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → ∀ u : ℕ → ℝ, IsFakePrimeMeasure K u →
      |classMass u q a - classMass pronicMeasure q a| ≤ ξ := fun a ha =>
    exists_level_classMass_close (hSq a ha).1 (hSq a ha).2 hξ
  choose! K₁ hK₁ using hclose
  refine ⟨q + S.sup K₁, fun K hK u hu => ?_⟩
  have hqK : q ∈ Icc 1 K := mem_Icc.mpr ⟨hq1, by omega⟩
  -- The target sits inside its classes.
  have hwin : targetMass u S ≤ ∑ a ∈ S, classMass u q a := by
    refine sum_le_sum fun a ha => ?_
    obtain ⟨h1, h2⟩ := hSq a ha
    have hmod : (a - 1 + 1) % q = a := by
      rw [show a - 1 + 1 = a by omega, Nat.mod_eq_of_lt h2]
    have hs := hu.summable_class hqK h1
    have hle := hs.le_tsum (a - 1) (fun i _ => by
      split_ifs
      · exact hu.nonneg i
      · exact le_rfl)
    simp only [hmod, if_true] at hle
    exact hle
  have hdiff : ∑ a ∈ S, classMass u q a ≤ ∑ a ∈ S, classMass pronicMeasure q a + (S.card : ℝ) * ξ := by
    have hterm : ∀ a ∈ S, classMass u q a ≤ classMass pronicMeasure q a + ξ := by
      intro a ha
      have hle : K₁ a ≤ K := by
        have h1 : K₁ a ≤ S.sup K₁ := Finset.le_sup ha
        omega
      have := abs_le.mp (hK₁ a ha K hle u hu)
      linarith
    refine (sum_le_sum hterm).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  have hP := sum_classMass_pronic_le hSq hq1
  have hξ2 : (S.card : ℝ) * ξ ≤ η / 2 := by
    rw [hξdef]
    have hb : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have e : (S.card : ℝ) * (η / (2 * ((S.card : ℝ) + 1))) = (η / 2) * ((S.card : ℝ) / ((S.card : ℝ) + 1)) := by
      field_simp
    rw [e]
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [div_le_one (by positivity)]
    linarith
  linarith

/-- The pronic mass of a window. -/
theorem targetMass_pronic_Ico {B : ℕ} (hB : 1 ≤ B) : targetMass pronicMeasure (Ico 1 B) = 1 - 1 / (B : ℝ) := by
  rw [targetMass_Ico, sum_range_pronic]
  have : ((B - 1 : ℕ) : ℝ) + 1 = B := by
    rw [Nat.cast_sub hB]
    push_cast
    ring
  rw [this]

/-- **The mass of a fixed window tends to the pronic mass.** -/
theorem exists_level_window_mass_le {B : ℕ} (hB : 2 ≤ B) {η : ℝ} (hη : 0 < η) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → ∀ u : ℕ → ℝ, IsFakePrimeMeasure K u →
      ∑ j ∈ range (B - 1), u j ≤ 1 - 1 / (B : ℝ) + η := by
  obtain ⟨K₀, h⟩ := exists_level_targetMass_le (S := Ico 1 B) (fun r hr => (mem_Ico.mp hr).1) hη
  refine ⟨K₀, fun K hK u hu => ?_⟩
  have := h K hK u hu
  rwa [targetMass_Ico, targetMass_pronic_Ico (by omega)] at this

/-- **Every finite shape is reached.** For every finite set `S` of positive integers there are integer shape producers, with multiplicity at least `m`
on `S`, of slope at most `m` times the pronic mass of `S`, up to `η`. -/
theorem exists_shape_producer {S : Finset ℕ} (hS : ∀ r ∈ S, 1 ≤ r) {η : ℝ} (hη : 0 < η) :
    ∃ (c : ℕ →₀ ℤ) (m K : ℕ), IsShapeProducer c m S ∧ AlphabetLE c K ∧
      stencilSlope c ≤ (m : ℝ) * (targetMass pronicMeasure S + η) := by
  obtain ⟨K₀, hK₀⟩ := exists_level_targetMass_le hS (η := η / 2) (by positivity)
  obtain ⟨K, hKdef⟩ : ∃ K, K = max K₀ (S.sup id + 2) := ⟨_, rfl⟩
  have hK0 : K₀ ≤ K := hKdef ▸ le_max_left _ _
  have hK2 : S.sup id + 2 ≤ K := hKdef ▸ le_max_right _ _
  have hSL : ∀ r ∈ S, 1 ≤ r ∧ r < lcmUpTo K := fun r hr => by
    have h1 : r ≤ S.sup id := Finset.le_sup (f := id) hr
    have hd := dvd_lcmUpTo (K := K) (k := S.sup id + 2) (mem_Icc.mpr ⟨by omega, hK2⟩)
    have h2 := Nat.le_of_dvd (lcmUpTo_pos K) hd
    exact ⟨hS r hr, by omega⟩
  obtain ⟨u, hu, -, -, hprod, -⟩ := exists_extremal_of_target (by omega : 2 ≤ K) hSL
  have hmass := hK₀ K hK0 u hu
  obtain ⟨c, m, hP, hal, hs⟩ := hprod (η / 2) (by positivity)
  refine ⟨c, m, K, hP, hal, hs.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m))⟩
  linarith

/-- **A spike at every integer.** For each `n ≥ 1` there are integer shape producers with multiplicity at least `m` at `n` and slope at most
`m (1/(n (n + 1)) + η)`. -/
theorem exists_spike_producer {n : ℕ} (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    ∃ (c : ℕ →₀ ℤ) (m K : ℕ), IsShapeProducer c m {n} ∧ AlphabetLE c K ∧
      stencilSlope c ≤ (m : ℝ) * (1 / ((n : ℝ) * ((n : ℝ) + 1)) + η) := by
  obtain ⟨c, m, K, hP, hal, hs⟩ := exists_shape_producer (S := {n})
    (fun r hr => by rw [mem_singleton.mp hr]; exact hn) hη
  refine ⟨c, m, K, hP, hal, ?_⟩
  have hval : targetMass pronicMeasure {n} = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [targetMass, sum_singleton, pronicMeasure, Nat.cast_sub hn]
    push_cast
    congr 2
    · ring
    · ring
  rwa [hval] at hs

/-- **Every window is reached.** For every `B ≥ 2` there are integer producers with window exactly `B` of arbitrarily small rate. -/
theorem exists_producer_at_window {B : ℕ} (hB : 2 ≤ B) {η : ℝ} (hη : 0 < η) :
    ∃ (c : ℕ →₀ ℤ) (m K : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧ rate c m B ≤ η := by
  obtain ⟨K₀, hK₀⟩ := exists_level_window_mass_le hB (η := η / 4) (by positivity)
  obtain ⟨K, hKdef⟩ : ∃ K, K = max (max K₀ 2) B := ⟨_, rfl⟩
  have hK0 : K₀ ≤ K := hKdef ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hK2 : 2 ≤ K := hKdef ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hKB : B ≤ K := hKdef ▸ le_max_right _ _
  have hBL : B ≤ lcmUpTo K :=
    Nat.le_of_dvd (lcmUpTo_pos K) (dvd_lcmUpTo (mem_Icc.mpr ⟨hB, hKB⟩))
  obtain ⟨u, hu, -, -, hprod⟩ := exists_extremal_fake_measure hK2 hB hBL
  have hmass := hK₀ K hK0 u hu
  obtain ⟨c, m, hP, hal, hs⟩ := hprod (η / 8) (by positivity)
  refine ⟨c, m, K, hP, hal, ?_⟩
  have hm := hP.m_pos
  have hd := hP.one_sub_pos
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hd2 : 1 / 2 ≤ 1 - 1 / (B : ℝ) := by
    have : 1 / (B : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hBR
    linarith
  have hsl : stencilSlope c ≤ (m : ℝ) * ((1 - 1 / (B : ℝ)) + η / 2) := by
    refine hs.trans (mul_le_mul_of_nonneg_left ?_ hm.le)
    linarith
  rw [rate, normSlope, sub_le_iff_le_add, div_le_iff₀ (mul_pos hm hd)]
  have hηd : η / 2 ≤ η * (1 - 1 / (B : ℝ)) := by nlinarith
  calc stencilSlope c ≤ (m : ℝ) * ((1 - 1 / (B : ℝ)) + η / 2) := hsl
    _ ≤ (m : ℝ) * ((1 - 1 / (B : ℝ)) + η * (1 - 1 / (B : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hm.le
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
