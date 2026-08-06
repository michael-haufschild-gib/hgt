import GaloisForLFunctions.HTGeometry.RationalRankStratumTopology
import Mathlib.Algebra.Polynomial.Roots

/-!
# Exact rational rank away from finitely many rational hyperplanes

Every real coordinate packet has arbitrarily close packets of any prescribed positive rational
rank which additionally avoid any prescribed finite family of proper affine hyperplanes defined
over the rationals.

The mechanism is a one-parameter rational rescaling of one nonzero entry.  Adding
`s * t ^ i * y i₁` to the `i`-th entry keeps every entry inside the rational span, and the entry at
`i₁` is rescaled by `1 + s * t ^ i₁`, so the span — hence the exact rank — is unchanged.  Along the
same family each rational functional moves affinely with slope the value at `t` of the polynomial
carrying its coefficients; choosing `t` off the finitely many roots makes every slope nonzero, so
each hyperplane is met for at most one parameter value.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- Exact positive rational rank is attained arbitrarily close to every packet. -/
theorem exists_exactRationalRank_close {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (x : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Fin n → ℝ, rationalCoordinateRank y = k ∧ ∀ i, dist (y i) (x i) < ε := by
  obtain ⟨r, rfl⟩ := exists_add_of_le hkn
  exact exists_exactRationalRank_close_add k r hk x ε hε

/-- A rational rescaling along one entry preserves the rational span. -/
theorem span_add_rat_smul_eq (y : Fin n → ℝ) (i₁ : Fin n) (lam : Fin n → ℚ)
    (hu : (1 : ℚ) + lam i₁ ≠ 0) :
    Submodule.span ℚ (Set.range fun i => y i + (lam i : ℝ) * y i₁) =
      Submodule.span ℚ (Set.range y) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨i, rfl⟩
    refine Submodule.add_mem _ (Submodule.subset_span ⟨i, rfl⟩) ?_
    simpa only [Rat.smul_def] using
      (Submodule.span ℚ (Set.range y)).smul_mem (lam i) (Submodule.subset_span ⟨i₁, rfl⟩)
  · have hz₁ : y i₁ ∈ Submodule.span ℚ (Set.range fun i => y i + (lam i : ℝ) * y i₁) := by
      have hzval : y i₁ + (lam i₁ : ℝ) * y i₁ = ((1 + lam i₁ : ℚ) : ℝ) * y i₁ := by
        push_cast
        ring
      have hgen : ((1 + lam i₁ : ℚ) : ℝ) * y i₁ ∈
          Submodule.span ℚ (Set.range fun i => y i + (lam i : ℝ) * y i₁) := by
        rw [← hzval]
        exact Submodule.subset_span ⟨i₁, rfl⟩
      have hscaled := (Submodule.span ℚ
        (Set.range fun i => y i + (lam i : ℝ) * y i₁)).smul_mem ((1 + lam i₁)⁻¹) hgen
      rw [Rat.smul_def] at hscaled
      have hne : ((1 + lam i₁ : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hu
      have hcast : (((1 + lam i₁)⁻¹ : ℚ) : ℝ) * (((1 + lam i₁ : ℚ) : ℝ) * y i₁) = y i₁ := by
        rw [Rat.cast_inv, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      rwa [hcast] at hscaled
    refine Submodule.span_le.2 ?_
    rintro z ⟨i, rfl⟩
    have hsub : y i = (y i + (lam i : ℝ) * y i₁) - (lam i : ℝ) * y i₁ := by ring
    rw [hsub]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨i, rfl⟩) ?_
    simpa only [Rat.smul_def] using
      (Submodule.span ℚ (Set.range fun i => y i + (lam i : ℝ) * y i₁)).smul_mem (lam i) hz₁

/-- The polynomial carrying a rational coefficient packet. -/
def ratPacketPoly (c : Fin n → ℚ) : Polynomial ℚ :=
  ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

theorem ratPacketPoly_coeff (c : Fin n → ℚ) (i : Fin n) :
    (ratPacketPoly c).coeff (i : ℕ) = c i := by
  rw [ratPacketPoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro hval
    exact hj (Fin.val_injective hval.symm)
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

theorem ratPacketPoly_ne_zero {c : Fin n → ℚ} (hc : c ≠ 0) : ratPacketPoly c ≠ 0 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc (funext hcon)
  intro hzero
  apply hi₀
  rw [← ratPacketPoly_coeff c i₀, hzero, Polynomial.coeff_zero]

theorem ratPacketPoly_eval (c : Fin n → ℚ) (t : ℚ) :
    (ratPacketPoly c).eval t = ∑ i : Fin n, c i * t ^ (i : ℕ) := by
  rw [ratPacketPoly, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- A nonzero rational polynomial has finitely many rational roots. -/
theorem finite_setOf_isRoot {p : Polynomial ℚ} (hp : p ≠ 0) :
    {x : ℚ | p.IsRoot x}.Finite := by
  refine Set.Finite.subset (p.roots.toFinset : Finset ℚ).finite_toSet ?_
  intro x hx
  simpa [Multiset.mem_toFinset, Polynomial.mem_roots hp] using hx

/-- A nonzero rational evaluation point exists for every finite family of nonzero rational
coefficient packets. -/
theorem exists_rat_eval_ne_zero {ι : Type*} [Fintype ι] (c : ι → Fin n → ℚ)
    (hc : ∀ a, c a ≠ 0) :
    ∃ t : ℚ, t ≠ 0 ∧ ∀ a, (ratPacketPoly (c a)).eval t ≠ 0 := by
  classical
  have hbad : ({0} ∪ ⋃ a : ι, {x : ℚ | (ratPacketPoly (c a)).IsRoot x}).Finite :=
    (Set.finite_singleton _).union
      (Set.finite_iUnion fun a => finite_setOf_isRoot (ratPacketPoly_ne_zero (hc a)))
  obtain ⟨t, ht⟩ := ((Set.infinite_univ (α := ℚ)).sdiff hbad).nonempty
  refine ⟨t, ?_, ?_⟩
  · intro hzero
    exact ht.2 (Or.inl (by simp [hzero]))
  · intro a hroot
    exact ht.2 (Or.inr (Set.mem_iUnion.mpr ⟨a, hroot⟩))

/-- **Exact rational rank off every rational hyperplane.**  For every packet, every tolerance,
every positive admissible rank and every finite family of proper affine rational hyperplanes there
is a packet of exactly that rank inside the tolerance which lies on none of the hyperplanes. -/
theorem exists_exactRationalRank_close_avoiding {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (x : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε)
    {ι : Type*} [Fintype ι] (c : ι → Fin n → ℚ) (hc : ∀ a, c a ≠ 0) (d : ι → ℚ) :
    ∃ y : Fin n → ℝ, rationalCoordinateRank y = k ∧ (∀ i, dist (y i) (x i) < ε) ∧
      ∀ a, (∑ i, (c a i : ℝ) * y i) ≠ (d a : ℝ) := by
  classical
  obtain ⟨y₀, hrank₀, hclose₀⟩ :=
    exists_exactRationalRank_close hk hkn x (half_pos hε)
  obtain ⟨i₁, hi₁⟩ : ∃ i, y₀ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hspan : Submodule.span ℚ (Set.range y₀) = ⊥ := by
      refine Submodule.span_eq_bot.mpr ?_
      rintro z ⟨i, rfl⟩
      exact hcon i
    rw [rationalCoordinateRank, hspan, finrank_bot] at hrank₀
    omega
  obtain ⟨t, ht0, hteval⟩ := exists_rat_eval_ne_zero c hc
  -- the functional along the rescaling family is affine with nonzero slope
  have hslope : ∀ (s : ℚ) (a : ι),
      (∑ i, (c a i : ℝ) * (y₀ i + ((s * t ^ (i : ℕ) : ℚ) : ℝ) * y₀ i₁)) =
        (∑ i, (c a i : ℝ) * y₀ i) +
          (s : ℝ) * (((ratPacketPoly (c a)).eval t : ℚ) : ℝ) * y₀ i₁ := by
    intro s a
    have hpoly : (((ratPacketPoly (c a)).eval t : ℚ) : ℝ)
        = ∑ i : Fin n, (c a i : ℝ) * (t : ℝ) ^ (i : ℕ) := by
      rw [ratPacketPoly_eval]
      push_cast
      ring
    rw [hpoly, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  -- the excluded parameters form a finite set
  have hbadfin :
      ({s : ℚ | (1 : ℚ) + s * t ^ (i₁ : ℕ) = 0} ∪
        ⋃ a : ι, {s : ℚ | (∑ i, (c a i : ℝ) * y₀ i) +
          (s : ℝ) * (((ratPacketPoly (c a)).eval t : ℚ) : ℝ) * y₀ i₁ = (d a : ℝ)}).Finite := by
    refine Set.Finite.union ?_ (Set.finite_iUnion fun a => ?_)
    · refine Set.Subsingleton.finite ?_
      intro s₁ hs₁ s₂ hs₂
      simp only [Set.mem_setOf_eq] at hs₁ hs₂
      have htpow : t ^ (i₁ : ℕ) ≠ 0 := pow_ne_zero _ ht0
      have hcancel : s₁ * t ^ (i₁ : ℕ) = s₂ * t ^ (i₁ : ℕ) := by linarith
      exact mul_right_cancel₀ htpow hcancel
    · refine Set.Subsingleton.finite ?_
      intro s₁ hs₁ s₂ hs₂
      simp only [Set.mem_setOf_eq] at hs₁ hs₂
      have hne : (((ratPacketPoly (c a)).eval t : ℚ) : ℝ) * y₀ i₁ ≠ 0 := by
        refine mul_ne_zero ?_ hi₁
        exact_mod_cast hteval a
      have hEq : (s₁ : ℝ) * ((((ratPacketPoly (c a)).eval t : ℚ) : ℝ) * y₀ i₁) =
          (s₂ : ℝ) * ((((ratPacketPoly (c a)).eval t : ℚ) : ℝ) * y₀ i₁) := by
        rw [← mul_assoc, ← mul_assoc]
        linarith
      exact_mod_cast mul_right_cancel₀ hne hEq
  -- a small admissible parameter exists
  have hCnonneg : (0 : ℝ) ≤ ∑ j : Fin n, |(t : ℝ) ^ (j : ℕ)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hDpos : (0 : ℝ) < (∑ j : Fin n, |(t : ℝ) ^ (j : ℕ)|) * |y₀ i₁| + 1 := by positivity
  obtain ⟨η, hη0, hηlt⟩ := exists_rat_btwn (div_pos (half_pos hε) hDpos)
  have hηQ : (0 : ℚ) < η := by exact_mod_cast hη0
  obtain ⟨s, hsmem, hsbad⟩ := ((Set.Ioo_infinite hηQ).sdiff hbadfin).nonempty
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hsmem.1
  have hsη : (s : ℝ) < (η : ℝ) := by exact_mod_cast hsmem.2
  refine ⟨fun i => y₀ i + ((s * t ^ (i : ℕ) : ℚ) : ℝ) * y₀ i₁, ?_, ?_, ?_⟩
  · have hu : (1 : ℚ) + (fun i : Fin n => s * t ^ (i : ℕ)) i₁ ≠ 0 := by
      intro hcon
      exact hsbad (Or.inl hcon)
    rw [rationalCoordinateRank,
      span_add_rat_smul_eq y₀ i₁ (fun i : Fin n => s * t ^ (i : ℕ)) hu]
    exact hrank₀
  · intro i
    have hstep : dist (y₀ i + ((s * t ^ (i : ℕ) : ℚ) : ℝ) * y₀ i₁) (y₀ i) < ε / 2 := by
      have hval : dist (y₀ i + ((s * t ^ (i : ℕ) : ℚ) : ℝ) * y₀ i₁) (y₀ i) =
          (s : ℝ) * |(t : ℝ) ^ (i : ℕ)| * |y₀ i₁| := by
        rw [Real.dist_eq,
          show y₀ i + ((s * t ^ (i : ℕ) : ℚ) : ℝ) * y₀ i₁ - y₀ i =
            ((s : ℝ) * (t : ℝ) ^ (i : ℕ)) * y₀ i₁ by push_cast; ring,
          abs_mul, abs_mul, abs_of_pos hs0]
      rw [hval]
      have hpowle : |(t : ℝ) ^ (i : ℕ)| ≤ ∑ j : Fin n, |(t : ℝ) ^ (j : ℕ)| :=
        Finset.single_le_sum (f := fun j : Fin n => |(t : ℝ) ^ (j : ℕ)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      have hmul : |(t : ℝ) ^ (i : ℕ)| * |y₀ i₁| ≤
          (∑ j : Fin n, |(t : ℝ) ^ (j : ℕ)|) * |y₀ i₁| + 1 := by
        have := mul_le_mul_of_nonneg_right hpowle (abs_nonneg (y₀ i₁))
        linarith
      have hbound : (s : ℝ) * |(t : ℝ) ^ (i : ℕ)| * |y₀ i₁| ≤
          (s : ℝ) * ((∑ j : Fin n, |(t : ℝ) ^ (j : ℕ)|) * |y₀ i₁| + 1) := by
        calc (s : ℝ) * |(t : ℝ) ^ (i : ℕ)| * |y₀ i₁|
            = (s : ℝ) * (|(t : ℝ) ^ (i : ℕ)| * |y₀ i₁|) := by ring
          _ ≤ (s : ℝ) * ((∑ j : Fin n, |(t : ℝ) ^ (j : ℕ)|) * |y₀ i₁| + 1) :=
              mul_le_mul_of_nonneg_left hmul hs0.le
      have hsmall : (s : ℝ) * ((∑ j : Fin n, |(t : ℝ) ^ (j : ℕ)|) * |y₀ i₁| + 1) < ε / 2 := by
        have hslt : (s : ℝ) < (ε / 2) / ((∑ j : Fin n, |(t : ℝ) ^ (j : ℕ)|) * |y₀ i₁| + 1) := by
          linarith
        have := mul_lt_mul_of_pos_right hslt hDpos
        rwa [div_mul_cancel₀ _ (ne_of_gt hDpos)] at this
      linarith
    calc dist (y₀ i + ((s * t ^ (i : ℕ) : ℚ) : ℝ) * y₀ i₁) (x i)
        ≤ dist (y₀ i + ((s * t ^ (i : ℕ) : ℚ) : ℝ) * y₀ i₁) (y₀ i) + dist (y₀ i) (x i) :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hstep (hclose₀ i)
      _ = ε := by ring
  · intro a hcon
    rw [hslope s a] at hcon
    exact hsbad (Or.inr (Set.mem_iUnion.mpr ⟨a, hcon⟩))

/-- **The exact-rank locus stays dense after deleting any finite family of rational hyperplanes.**
This is the topological form of the avoidance theorem. -/
theorem dense_exactRationalRank_avoiding {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {ι : Type*} [Fintype ι] (c : ι → Fin n → ℚ) (hc : ∀ a, c a ≠ 0) (d : ι → ℚ) :
    Dense ({ω : Fin n → ℝ | rationalCoordinateRank ω = k} \
      ⋃ a : ι, {ω : Fin n → ℝ | (∑ i, (c a i : ℝ) * ω i) = (d a : ℝ)}) := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨y, hrank, hclose, havoid⟩ := exists_exactRationalRank_close_avoiding hk hkn x hε c hc d
  refine ⟨y, ?_, hrank, ?_⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hε]
    exact hclose
  · simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
    exact havoid

/-- A single coordinate read off by a rational indicator functional. -/
theorem sum_single_mul (i : Fin n) (y : Fin n → ℝ) :
    (∑ i' : Fin n, (((Pi.single i (1 : ℚ) : Fin n → ℚ) i' : ℚ) : ℝ) * y i') = y i := by
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- A coordinate difference read off by a rational functional. -/
theorem sum_singleSub_mul (a b : Fin n) (y : Fin n → ℝ) :
    (∑ i' : Fin n, ((((Pi.single a (1 : ℚ) : Fin n → ℚ)
        - (Pi.single b (1 : ℚ) : Fin n → ℚ)) i' : ℚ) : ℝ) * y i') = y a - y b := by
  classical
  have hsplit : ∀ i' : Fin n,
      ((((Pi.single a (1 : ℚ) : Fin n → ℚ) - (Pi.single b (1 : ℚ) : Fin n → ℚ)) i' : ℚ) : ℝ)
          * y i'
        = (((Pi.single a (1 : ℚ) : Fin n → ℚ) i' : ℚ) : ℝ) * y i'
          - (((Pi.single b (1 : ℚ) : Fin n → ℚ) i' : ℚ) : ℝ) * y i' := by
    intro i'
    simp only [Pi.sub_apply]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i' _ => hsplit i', Finset.sum_sub_distrib, sum_single_mul,
    sum_single_mul]

/-- **Exact rank with nonzero, pairwise distinct entries.**  Every packet has arbitrarily close
packets of any prescribed positive rational rank whose entries are all nonzero and pairwise
distinct: the coordinate hyperplanes and the diagonal hyperplanes are a finite rational family, so
the avoidance theorem applies to them. -/
theorem exists_exactRationalRank_close_distinct {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (x : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Fin n → ℝ, rationalCoordinateRank y = k ∧ (∀ i, dist (y i) (x i) < ε) ∧
      (∀ i, y i ≠ 0) ∧ ∀ i j, i ≠ j → y i ≠ y j := by
  classical
  set c : (Fin n) ⊕ {p : Fin n × Fin n // p.1 ≠ p.2} → Fin n → ℚ := fun a =>
    match a with
    | Sum.inl i => (Pi.single i (1 : ℚ) : Fin n → ℚ)
    | Sum.inr p =>
        (Pi.single p.1.1 (1 : ℚ) : Fin n → ℚ) - (Pi.single p.1.2 (1 : ℚ) : Fin n → ℚ) with hcdef
  have hc : ∀ a, c a ≠ 0 := by
    rintro (i | ⟨⟨a, b⟩, hab⟩) hcon
    · have := congrFun hcon i
      simp [hcdef] at this
    · have := congrFun hcon a
      simp only [hcdef, Pi.sub_apply, Pi.zero_apply, Pi.single_apply,
        if_neg (fun h : a = b => hab h)] at this
      norm_num at this
  obtain ⟨y, hrank, hclose, havoid⟩ :=
    exists_exactRationalRank_close_avoiding hk hkn x hε c hc (fun _ => 0)
  refine ⟨y, hrank, hclose, fun i => ?_, fun i j hij => ?_⟩
  · have h := havoid (Sum.inl i)
    rw [show ((0 : ℚ) : ℝ) = 0 by norm_num] at h
    have hval : (∑ i' : Fin n, ((c (Sum.inl i) i' : ℚ) : ℝ) * y i') = y i := by
      simpa [hcdef] using sum_single_mul i y
    rw [hval] at h
    exact h
  · have h := havoid (Sum.inr ⟨(i, j), hij⟩)
    rw [show ((0 : ℚ) : ℝ) = 0 by norm_num] at h
    have hval : (∑ i' : Fin n, ((c (Sum.inr ⟨(i, j), hij⟩) i' : ℚ) : ℝ) * y i') = y i - y j := by
      simpa [hcdef] using sum_singleSub_mul i j y
    rw [hval] at h
    exact fun hcon => h (by rw [hcon, sub_self])

end

end GaloisForLFunctions.HTGeometry
