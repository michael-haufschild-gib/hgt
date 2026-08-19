import GaloisForLFunctions.HTGeometry.HalfLineExponentialReader

/-!
# The residual is the limit of the finite co-distances

The finite Gram--Schmidt lengths of the deferred exponential systems are the distances from one
exponential to the span of finitely many others.  Those spans increase to a dense subspace of the
closed co-span, so the lengths decrease to the length of the orthogonal projection residual.

This is the bridge that turns the closed-form finite co-distance into the exact norm of the
canonical reader.
-/

open Filter Topology Finset MeasureTheory
open scoped InnerProductSpace
open InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {lam : ℕ → ℝ} (hpos : ∀ k, 0 < lam k)

/-- The span of the exponentials with index at most `N` other than the `n`-th. -/
def expCoSpanFin (lam : ℕ → ℝ) (hpos : ∀ k, 0 < lam k) (n N : ℕ) :
    Submodule ℂ (Lp ℂ 2 halfLineLaplaceMeasure) :=
  Submodule.span ℂ ((expSystem lam hpos) '' {m : ℕ | m ≠ n ∧ m ≤ N})

theorem expCoSpanFin_mono {n N M : ℕ} (hNM : N ≤ M) :
    expCoSpanFin lam hpos n N ≤ expCoSpanFin lam hpos n M := by
  refine Submodule.span_mono (Set.image_mono ?_)
  rintro m ⟨hmn, hm⟩
  exact ⟨hmn, hm.trans hNM⟩

theorem expCoSpanFin_le_expCoSpan (n N : ℕ) :
    expCoSpanFin lam hpos n N ≤ expCoSpan lam hpos n := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, ⟨hmn, -⟩, rfl⟩
  exact expSystem_mem_expCoSpan hpos hmn

/-- The deferred system spans exactly the finite co-span. -/
theorem image_coIdx_Iio (n N : ℕ) (hn : n ≤ N) :
    (fun k => expSystem lam hpos (coIdx n N k)) '' Set.Iio N =
      (expSystem lam hpos) '' {m : ℕ | m ≠ n ∧ m ≤ N} := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Set.mem_Iio] at hk
    refine ⟨coIdx n N k, ⟨coIdx_ne_of_ne (Nat.ne_of_lt hk), ?_⟩, rfl⟩
    have := coIdx_lt_of_lt (n := n) hk
    omega
  · rintro ⟨m, ⟨hmn, hm⟩, rfl⟩
    have hmem : m ∈ (Finset.range (N + 1)).erase n := by
      rw [Finset.mem_erase, Finset.mem_range]
      exact ⟨hmn, by omega⟩
    rw [← image_coIdx hn, Finset.mem_image] at hmem
    obtain ⟨k, hk, hkm⟩ := hmem
    rw [Finset.mem_range] at hk
    exact ⟨k, hk, congrArg (expSystem lam hpos) hkm⟩

theorem span_gramSchmidt_coSystem (n N : ℕ) (hn : n ≤ N) :
    Submodule.span ℂ
        (gramSchmidt ℂ (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) ''
          Set.Iio N) = expCoSpanFin lam hpos n N := by
  rw [span_gramSchmidt_Iio, expCoSpanFin]
  congr 1
  exact image_coIdx_Iio hpos n N hn

/-! ## The Gram--Schmidt length is the finite co-distance -/

theorem isLeast_norm_gramSchmidt_coSystem (n N : ℕ) (hn : n ≤ N) :
    IsLeast ((fun w => ‖expSystem lam hpos n - w‖) '' (expCoSpanFin lam hpos n N))
      ‖gramSchmidt ℂ (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N‖ := by
  have h := isLeast_norm_gramSchmidt
    (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N
  rw [span_gramSchmidt_coSystem hpos n N hn] at h
  have hval : expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _) N =
      expSystem lam hpos n := by
    simp only [expSystem, coIdx_self]
  rwa [hval] at h

/-! ## Comparison with the projection residual -/

theorem norm_expResidual_le_norm_sub {n : ℕ} {w : Lp ℂ 2 halfLineLaplaceMeasure}
    (hw : w ∈ expCoSpan lam hpos n) :
    ‖expResidual lam hpos n‖ ≤ ‖expSystem lam hpos n - w‖ := by
  have hproj : (expCoSpan lam hpos n).starProjection (expSystem lam hpos n) - w ∈
      expCoSpan lam hpos n :=
    Submodule.sub_mem _ ((expCoSpan lam hpos n).starProjection_apply_mem _) hw
  have horth : inner ℂ
      ((expCoSpan lam hpos n).starProjection (expSystem lam hpos n) - w)
      (expResidual lam hpos n) = 0 :=
    (Submodule.mem_orthogonal _ _).mp (expResidual_mem_orthogonal hpos n) _ hproj
  have hsplit : expSystem lam hpos n - w =
      expResidual lam hpos n +
        ((expCoSpan lam hpos n).starProjection (expSystem lam hpos n) - w) := by
    rw [expResidual]
    abel
  have hpy : ‖expSystem lam hpos n - w‖ * ‖expSystem lam hpos n - w‖ =
      ‖expResidual lam hpos n‖ * ‖expResidual lam hpos n‖ +
        ‖(expCoSpan lam hpos n).starProjection (expSystem lam hpos n) - w‖ *
          ‖(expCoSpan lam hpos n).starProjection (expSystem lam hpos n) - w‖ := by
    have hinner : inner ℂ (expResidual lam hpos n)
        ((expCoSpan lam hpos n).starProjection (expSystem lam hpos n) - w) = 0 := by
      rw [← inner_conj_symm, horth, map_zero]
    rw [hsplit]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hinner
  have hle : ‖expResidual lam hpos n‖ * ‖expResidual lam hpos n‖ ≤
      ‖expSystem lam hpos n - w‖ * ‖expSystem lam hpos n - w‖ := by
    rw [hpy]
    have hnn : (0 : ℝ) ≤
        ‖(expCoSpan lam hpos n).starProjection (expSystem lam hpos n) - w‖ *
          ‖(expCoSpan lam hpos n).starProjection (expSystem lam hpos n) - w‖ := by positivity
    linarith
  nlinarith [hle, norm_nonneg (expResidual lam hpos n),
    norm_nonneg (expSystem lam hpos n - w)]

theorem norm_expResidual_le_gramSchmidt (n N : ℕ) (hn : n ≤ N) :
    ‖expResidual lam hpos n‖ ≤
      ‖gramSchmidt ℂ (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N‖ := by
  obtain ⟨w, hw, hval⟩ := (isLeast_norm_gramSchmidt_coSystem hpos n N hn).1
  rw [← hval]
  exact norm_expResidual_le_norm_sub hpos (expCoSpanFin_le_expCoSpan hpos n N hw)

/-- The finite co-distances are antitone. -/
theorem gramSchmidt_coSystem_antitone {n N M : ℕ} (hn : n ≤ N) (hNM : N ≤ M) :
    ‖gramSchmidt ℂ (expSystem (fun k => lam (coIdx n M k)) (fun _ => hpos _)) M‖ ≤
      ‖gramSchmidt ℂ (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N‖ := by
  obtain ⟨w, hw, hval⟩ := (isLeast_norm_gramSchmidt_coSystem hpos n N hn).1
  rw [← hval]
  refine (isLeast_norm_gramSchmidt_coSystem hpos n M (hn.trans hNM)).2 ?_
  exact ⟨w, expCoSpanFin_mono hpos hNM hw, rfl⟩

/-! ## The residual equals the limiting co-distance -/

/-- Every algebraic combination of the other exponentials is supported below some cutoff. -/
theorem exists_mem_expCoSpanFin {n : ℕ} {w : Lp ℂ 2 halfLineLaplaceMeasure}
    (hw : w ∈ Submodule.span ℂ ((expSystem lam hpos) '' {m : ℕ | m ≠ n})) :
    ∃ N : ℕ, n ≤ N ∧ w ∈ expCoSpanFin lam hpos n N := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, hmn, rfl⟩ := hx
      exact ⟨max m n, le_max_right _ _,
        Submodule.subset_span ⟨m, ⟨hmn, le_max_left _ _⟩, rfl⟩⟩
  | zero => exact ⟨n, le_refl n, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨Nx, hnx, hxm⟩ := hx
      obtain ⟨Ny, -, hym⟩ := hy
      exact ⟨max Nx Ny, le_trans hnx (le_max_left _ _),
        Submodule.add_mem _ (expCoSpanFin_mono hpos (le_max_left _ _) hxm)
          (expCoSpanFin_mono hpos (le_max_right _ _) hym)⟩
  | smul c x _ hx =>
      obtain ⟨N, hn, hxm⟩ := hx
      exact ⟨N, hn, Submodule.smul_mem _ _ hxm⟩

/-- **The residual is the limit of the finite co-distances.** -/
theorem norm_expResidual_eq_of_tendsto {n : ℕ} {L : ℝ}
    (hL : Filter.Tendsto
      (fun N => ‖gramSchmidt ℂ (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N‖)
      Filter.atTop (nhds L)) :
    ‖expResidual lam hpos n‖ = L := by
  refine le_antisymm ?_ ?_
  · refine ge_of_tendsto hL ?_
    filter_upwards [Filter.eventually_ge_atTop n] with N hN
    exact norm_expResidual_le_gramSchmidt hpos n N hN
  · refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hproj : (expCoSpan lam hpos n).starProjection (expSystem lam hpos n) ∈
        closure ((Submodule.span ℂ ((expSystem lam hpos) '' {m : ℕ | m ≠ n}) :
          Submodule ℂ (Lp ℂ 2 halfLineLaplaceMeasure)) : Set (Lp ℂ 2 halfLineLaplaceMeasure)) :=
      (expCoSpan lam hpos n).starProjection_apply_mem _
    obtain ⟨w, hwmem, hwdist⟩ := Metric.mem_closure_iff.mp hproj ε hε
    obtain ⟨N, hnN, hwN⟩ := exists_mem_expCoSpanFin hpos hwmem
    have hgs : ‖gramSchmidt ℂ
        (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N‖ ≤
        ‖expSystem lam hpos n - w‖ :=
      (isLeast_norm_gramSchmidt_coSystem hpos n N hnN).2 ⟨w, hwN, rfl⟩
    have hLle : L ≤ ‖gramSchmidt ℂ
        (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N‖ := by
      refine le_of_tendsto hL ?_
      filter_upwards [Filter.eventually_ge_atTop N] with M hM
      exact gramSchmidt_coSystem_antitone hpos hnN hM
    have hsplit : expSystem lam hpos n - w = expResidual lam hpos n +
        ((expCoSpan lam hpos n).starProjection (expSystem lam hpos n) - w) := by
      rw [expResidual]
      abel
    have hclose : ‖(expCoSpan lam hpos n).starProjection (expSystem lam hpos n) - w‖ ≤ ε := by
      rw [← dist_eq_norm]
      exact le_of_lt hwdist
    have htri : ‖expSystem lam hpos n - w‖ ≤ ‖expResidual lam hpos n‖ + ε := by
      rw [hsplit]
      exact le_trans (norm_add_le _ _) (by linarith)
    linarith


end

end GaloisForLFunctions.HTGeometry
