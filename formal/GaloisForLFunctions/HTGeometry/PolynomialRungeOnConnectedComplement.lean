import GaloisForLFunctions.HTGeometry.RungeDensity
import GaloisForLFunctions.HTGeometry.EntireDividedDifferenceContour

/-!
# Polynomial Runge approximation on compact sets with connected complement

If `K ⊂ ℂ` is compact with `ℂ \ K` connected and `F` is analytic on an open set containing `K`,
then `F` is uniformly approximable on `K` by polynomials
(`approxOn_polyFun_of_analyticOnNhd`).

The grid-contour representation of the differentially algebraic Runge theorem is reused: on a
selection of grid squares covering `K` inside the domain, the contour functional (the signed sum of
the surviving edge integrals of `F(w)/(w − z)`) equals `2πi F(z)` at every point of `K` off the
grid lines.  Each surviving edge misses `K`, so its edge integral is a uniform limit on `K` of
Riemann sums of Cauchy kernels with poles on the edge, and a Cauchy kernel with pole `w ∉ K` is
approximable on `K` by polynomials: the set of such poles is open and relatively closed in the
connected set `ℂ \ K` (one-step pole transfer by the geometric series) and contains the far
poles (expansion in powers of `z`), hence is all of `ℂ \ K`.  The contour functional is
differentiable, hence continuous, at every point of `K`, so the identity `Φ = 2πi F` extends from
the open floor square to the whole of `K`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Metric Filter Topology

noncomputable section

/-! ## The polynomial class -/

/-- The polynomial functions `ℂ → ℂ`. -/
def PolyFun : Set (ℂ → ℂ) := Set.range fun P : Polynomial ℂ => fun z => P.eval z

theorem polyFun_zero : (fun _ : ℂ => (0 : ℂ)) ∈ PolyFun :=
  ⟨0, by funext z; simp⟩

theorem polyFun_const (c : ℂ) : (fun _ : ℂ => c) ∈ PolyFun :=
  ⟨Polynomial.C c, by funext z; simp⟩

theorem polyFun_add : ∀ g₁ ∈ PolyFun, ∀ g₂ ∈ PolyFun, (fun z => g₁ z + g₂ z) ∈ PolyFun := by
  rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
  exact ⟨P + Q, by funext z; simp [Polynomial.eval_add]⟩

theorem polyFun_smul : ∀ (c : ℂ), ∀ g ∈ PolyFun, (fun z => c * g z) ∈ PolyFun := by
  rintro c _ ⟨P, rfl⟩
  exact ⟨Polynomial.C c * P, by funext z; simp [Polynomial.eval_mul]⟩

theorem polyFun_mul : ∀ g₁ ∈ PolyFun, ∀ g₂ ∈ PolyFun, (fun z => g₁ z * g₂ z) ∈ PolyFun := by
  rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
  exact ⟨P * Q, by funext z; simp [Polynomial.eval_mul]⟩

/-- The truncated expansion of a far pole in powers of `z` is a polynomial. -/
theorem polyFun_infPushSum (a : ℂ) (N : ℕ) : (fun z => infPushSum a N z) ∈ PolyFun := by
  classical
  refine ⟨-∑ n ∈ Finset.range N, Polynomial.C ((a⁻¹) ^ (n + 1)) * Polynomial.X ^ n, ?_⟩
  funext z
  rw [infPushSum]
  simp [Polynomial.eval_finsetSum]
  ring_nf

/-! ## Products of approximable bounded functions -/

/-- Products of uniformly approximable bounded functions are approximable, for a class closed
under products. -/
theorem approxOn_mul_of_bounded {K : Set ℂ} {C : Set (ℂ → ℂ)}
    (hC : ∀ g₁ ∈ C, ∀ g₂ ∈ C, (fun z => g₁ z * g₂ z) ∈ C)
    {f₁ f₂ : ℂ → ℂ} {M₁ M₂ : ℝ} (hM₁ : ∀ z ∈ K, ‖f₁ z‖ ≤ M₁) (hM₂ : ∀ z ∈ K, ‖f₂ z‖ ≤ M₂)
    (h₁ : ApproxOn K C f₁) (h₂ : ApproxOn K C f₂) :
    ApproxOn K C (fun z => f₁ z * f₂ z) := by
  intro ε hε
  set A : ℝ := max M₁ 0 + max M₂ 0 + 2 with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set η : ℝ := min 1 (ε / A) with hη
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηA : η * A ≤ ε := by
    calc η * A ≤ (ε / A) * A := mul_le_mul_of_nonneg_right (min_le_right _ _) hApos.le
      _ = ε := by field_simp
  obtain ⟨g₁, hg₁C, hg₁⟩ := h₁ η hηpos
  obtain ⟨g₂, hg₂C, hg₂⟩ := h₂ η hηpos
  refine ⟨fun z => g₁ z * g₂ z, hC g₁ hg₁C g₂ hg₂C, fun z hz => ?_⟩
  have h1 := hg₁ z hz
  have h2 := hg₂ z hz
  have hf₁ := hM₁ z hz
  have hf₂ := hM₂ z hz
  have hg₂b : ‖g₂ z‖ ≤ max M₂ 0 + 1 := by
    calc ‖g₂ z‖ = ‖f₂ z - (f₂ z - g₂ z)‖ := by congr 1; ring
      _ ≤ ‖f₂ z‖ + ‖f₂ z - g₂ z‖ := norm_sub_le _ _
      _ ≤ max M₂ 0 + 1 := add_le_add (hf₂.trans (le_max_left _ _)) (h2.trans hη1)
  have hid : f₁ z * f₂ z - g₁ z * g₂ z = f₁ z * (f₂ z - g₂ z) + (f₁ z - g₁ z) * g₂ z := by ring
  rw [hid]
  calc ‖f₁ z * (f₂ z - g₂ z) + (f₁ z - g₁ z) * g₂ z‖
      ≤ ‖f₁ z‖ * ‖f₂ z - g₂ z‖ + ‖f₁ z - g₁ z‖ * ‖g₂ z‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ max M₁ 0 * η + η * (max M₂ 0 + 1) :=
        add_le_add (mul_le_mul (hf₁.trans (le_max_left _ _)) h2 (norm_nonneg _) (le_max_right _ _))
          (mul_le_mul h1 hg₂b (norm_nonneg _) hηpos.le)
    _ = η * (A - 1) := by rw [hA]; ring
    _ ≤ ε := by nlinarith

/-- Powers of a Cauchy kernel bounded away from `K` are approximable once the kernel is. -/
theorem approxOn_polyFun_cauchyKernel_pow {K : Set ℂ} {w : ℂ} {d : ℝ} (hd0 : 0 < d)
    (hK : ∀ z ∈ K, d ≤ ‖z - w‖) (h : ApproxOn K PolyFun (fun z => (z - w)⁻¹)) (k : ℕ) :
    ApproxOn K PolyFun (fun z => ((z - w)⁻¹) ^ k) := by
  have hbound : ∀ z ∈ K, ‖(z - w)⁻¹‖ ≤ d⁻¹ := fun z hz => by
    rw [norm_inv]
    exact inv_anti₀ hd0 (hK z hz)
  induction k with
  | zero =>
    refine approxOn_of_mem ?_
    simpa using polyFun_const (1 : ℂ)
  | succ k ih =>
    have hfun : (fun z => ((z - w)⁻¹) ^ (k + 1)) = fun z => (z - w)⁻¹ * ((z - w)⁻¹) ^ k := by
      funext z
      ring
    rw [hfun]
    refine approxOn_mul_of_bounded polyFun_mul hbound (M₂ := d⁻¹ ^ k) (fun z hz => ?_) h ih
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound z hz) k

/-! ## Pole pushing along a connected complement -/

/-- **One-step pole transfer.**  If the kernel with pole `w` is approximable on `K` and
`‖w' − w‖ < d ≤ ‖z − w‖` on `K`, then the kernel with pole `w'` is approximable. -/
theorem approxOn_polyFun_cauchyKernel_of_near {K : Set ℂ} {w w' : ℂ} {d : ℝ} (hd0 : 0 < d)
    (hw : ‖w' - w‖ < d) (hK : ∀ z ∈ K, d ≤ ‖z - w‖)
    (h : ApproxOn K PolyFun (fun z => (z - w)⁻¹)) :
    ApproxOn K PolyFun (fun z => (z - w')⁻¹) := by
  classical
  refine approxOn_of_approxOn fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_polePush_small (K := K) (a := w') (b := w) (norm_nonneg _) hw le_rfl
    hK hε
  refine ⟨fun z => polePushSum w' w N z, ?_, hN⟩
  have hfun : (fun z => polePushSum w' w N z)
      = fun z => ∑ n ∈ Finset.range N, (w' - w) ^ n * ((z - w)⁻¹) ^ (n + 1) := by
    funext z
    rfl
  rw [hfun]
  exact approxOn_finsetSum polyFun_zero polyFun_add (Finset.range N) fun n _ =>
    approxOn_smul polyFun_smul _ (approxOn_polyFun_cauchyKernel_pow hd0 hK h (n + 1))

/-- **Far poles** are approximable by polynomials. -/
theorem approxOn_polyFun_cauchyKernel_of_far {K : Set ℂ} {w : ℂ} {R : ℝ} (hR : 0 < R)
    (hK : ∀ z ∈ K, ‖z‖ ≤ R) (hw : 2 * R ≤ ‖w‖) :
    ApproxOn K PolyFun (fun z => (z - w)⁻¹) := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_infPush_small hR hK hw hε
  exact ⟨fun z => infPushSum w N z, polyFun_infPushSum w N, hN⟩

/-- **Pole pushing to infinity along a connected complement.**  For `K` compact with `ℂ \ K`
connected and `w ∉ K`, the Cauchy kernel `z ↦ (z − w)⁻¹` is uniformly approximable on `K` by
polynomials. -/
theorem approxOn_polyFun_cauchyKernel_of_isPreconnected_compl {K : Set ℂ} (hK : IsCompact K)
    (hconn : IsPreconnected Kᶜ) {w : ℂ} (hw : w ∉ K) :
    ApproxOn K PolyFun (fun z => (z - w)⁻¹) := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · intro ε _
    exact ⟨fun _ => 0, polyFun_zero, fun z hz => by rw [hemp] at hz; exact hz.elim⟩
  have hdist : ∀ w₀ ∉ K, 0 < infDist w₀ K ∧ ∀ z ∈ K, infDist w₀ K ≤ ‖z - w₀‖ := fun w₀ hw₀ =>
    ⟨(hK.isClosed.notMem_iff_infDist_pos hne).mp hw₀, fun z hz => by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact infDist_le_dist_of_mem hz⟩
  set A : Set ℂ := {w | w ∉ K ∧ ApproxOn K PolyFun (fun z => (z - w)⁻¹)} with hA
  set B : Set ℂ := {w | w ∉ K ∧ ¬ ApproxOn K PolyFun (fun z => (z - w)⁻¹)} with hB
  have hAopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    rintro w₀ ⟨hw₀, happ⟩
    obtain ⟨hd, hdK⟩ := hdist w₀ hw₀
    refine ⟨infDist w₀ K, hd, fun w' hw' => ?_⟩
    rw [mem_ball, dist_eq_norm] at hw'
    have hw'K : w' ∉ K := fun h => by
      have := hdK w' h
      linarith
    exact ⟨hw'K, approxOn_polyFun_cauchyKernel_of_near hd hw' hdK happ⟩
  have hBopen : IsOpen B := by
    rw [Metric.isOpen_iff]
    rintro w₀ ⟨hw₀, hnapp⟩
    obtain ⟨hd, hdK⟩ := hdist w₀ hw₀
    refine ⟨infDist w₀ K / 2, by positivity, fun w' hw' => ?_⟩
    rw [mem_ball, dist_eq_norm] at hw'
    have hdK' : ∀ z ∈ K, infDist w₀ K / 2 ≤ ‖z - w'‖ := fun z hz => by
      have h1 := hdK z hz
      have h2 := norm_sub_le_norm_sub_add_norm_sub z w' w₀
      linarith
    have hw'K : w' ∉ K := fun h => by
      have := hdK' w' h
      rw [sub_self, norm_zero] at this
      linarith
    refine ⟨hw'K, fun happ' => hnapp ?_⟩
    exact approxOn_polyFun_cauchyKernel_of_near (by positivity) (by rw [norm_sub_rev]; exact hw')
      hdK' happ'
  have hcover : Kᶜ ⊆ A ∪ B := fun w hw => by
    by_cases h : ApproxOn K PolyFun (fun z => (z - w)⁻¹)
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨hw, h⟩
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro w ⟨_, h⟩ ⟨_, h'⟩
    exact h' h
  have hAne : (Kᶜ ∩ A).Nonempty := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    set R' : ℝ := max R 0 + 1 with hR'
    have hR'pos : 0 < R' := by rw [hR']; positivity
    have hKR' : ∀ z ∈ K, ‖z‖ ≤ R' := fun z hz => by
      have := hR hz
      rw [mem_closedBall, dist_zero_right] at this
      rw [hR']
      linarith [le_max_left R 0]
    have hwnorm : ‖((2 * R' : ℝ) : ℂ)‖ = 2 * R' := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hwK : ((2 * R' : ℝ) : ℂ) ∉ K := fun h => by
      have := hKR' _ h
      rw [hwnorm] at this
      linarith
    exact ⟨((2 * R' : ℝ) : ℂ), hwK, hwK,
      approxOn_polyFun_cauchyKernel_of_far hR'pos hKR' (by rw [hwnorm])⟩
  exact (IsPreconnected.subset_left_of_subset_union hAopen hBopen hdisj hcover hAne hconn hw).2

/-! ## Edge integrals and the contour functional -/

/-- **Edge integrals are approximable by polynomials** when every pole on the edge is. -/
theorem approxOn_polyFun_edgeCauchyIntegral {K : Set ℂ} (hKc : IsCompact K)
    {F : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hFc : ContinuousOn F (γ '' Icc a b))
    (hne : ∀ x ∈ Icc a b, ∀ z ∈ K, γ x ≠ z)
    (hpole : ∀ x ∈ Icc a b, ApproxOn K PolyFun (fun z => (z - γ x)⁻¹)) :
    ApproxOn K PolyFun (fun z => edgeCauchyIntegral F γ a b z) := by
  classical
  refine approxOn_of_approxOn ?_
  intro ε hε
  obtain ⟨N, hNpos, hN⟩ := exists_edgeCauchyRiemann_approx hab hKc hγ hFc hne hε
  refine ⟨fun z => edgeCauchyRiemann F γ a b N z, ?_, hN⟩
  have hterm : ∀ i ∈ Finset.range N,
      ApproxOn K PolyFun
        (fun z => (((b - a) / N : ℝ)) • (F (γ (uniformNode a b N i)) *
          (γ (uniformNode a b N i) - z)⁻¹)) := by
    intro i hi
    have hnode : uniformNode a b N i ∈ Icc a b :=
      uniformNode_mem_Icc hab hNpos (le_of_lt (Finset.mem_range.1 hi))
    have hbase := hpole _ hnode
    have hfun : (fun z => (((b - a) / N : ℝ)) • (F (γ (uniformNode a b N i)) *
        (γ (uniformNode a b N i) - z)⁻¹))
        = fun z => (-(((b - a) / N : ℝ) : ℂ) * F (γ (uniformNode a b N i))) *
            (z - γ (uniformNode a b N i))⁻¹ := by
      funext z
      have hinv : (γ (uniformNode a b N i) - z)⁻¹ = -((z - γ (uniformNode a b N i))⁻¹) := by
        rw [show γ (uniformNode a b N i) - z = -(z - γ (uniformNode a b N i)) by ring, inv_neg]
      rw [hinv, Complex.real_smul]
      ring
    rw [hfun]
    exact approxOn_smul polyFun_smul _ hbase
  have hsum := approxOn_finsetSum (K := K) (C := PolyFun) polyFun_zero polyFun_add
    (Finset.range N) hterm
  have hfun : (fun z => edgeCauchyRiemann F γ a b N z)
      = fun z => ∑ i ∈ Finset.range N, (((b - a) / N : ℝ)) • (F (γ (uniformNode a b N i)) *
          (γ (uniformNode a b N i) - z)⁻¹) := by
    funext z
    rfl
  rw [hfun]
  exact hsum

variable {Ω K : Set ℂ} {s R : ℝ} {S : Finset (ℤ × ℤ)} {F : ℂ → ℂ}

/-- A surviving horizontal edge integral is approximable by polynomials on `K`. -/
theorem approxOn_polyFun_gridH (hK : IsCompact K) (hconn : IsPreconnected Kᶜ) (hs : 0 < s)
    (hS : GridSelects S s K) (hmemS : ∀ q : ℤ × ℤ, q ∈ S ↔ SelSquare s Ω R q)
    (hF : AnalyticOnNhd ℂ F Ω) {p : ℤ × ℤ} (hne : hCoeff S p ≠ 0) :
    ApproxOn K PolyFun (fun z => gridH (fun w => F w * (w - z)⁻¹) s p.1 p.2) := by
  classical
  set γ : ℝ → ℂ := fun x => (x : ℂ) + ((s * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I with hγdef
  have hab : s * (p.1 : ℝ) ≤ s * ((p.1 : ℝ) + 1) := by nlinarith
  have hboth : ∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)),
      γ x ∈ gridSquare s p.1 p.2 ∧ γ x ∈ gridSquare s p.1 (p.2 - 1) :=
    fun x hx => hEdgePoint_mem_squares hs p hx
  have hedgeΩ : ∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)), γ x ∈ Ω := by
    intro x hx
    rcases exists_notSelSquare_of_hCoeff_ne hmemS hne with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2.1 (hboth x hx).2
    · exact h1.1 (hboth x hx).1
  have hFc : ContinuousOn F (γ '' Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1))) := by
    rintro w ⟨x, hx, rfl⟩
    exact ((hF _ (hedgeΩ x hx)).continuousAt).continuousWithinAt
  have hγc : ContinuousOn γ (Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1))) := by
    apply Continuous.continuousOn
    rw [hγdef]
    fun_prop
  have hne' : ∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)), ∀ z ∈ K, γ x ≠ z := by
    intro x hx z hz hxz
    refine hEdge_avoids_of_hCoeff_ne_zero hs hS hne hz ⟨?_, ?_, ?_⟩
    · rw [← hxz, hγdef]; exact (cornerPt_re _ _).symm ▸ hx.1
    · rw [← hxz, hγdef]; exact (cornerPt_re _ _).symm ▸ hx.2
    · rw [← hxz, hγdef]; exact cornerPt_im _ _
  have hpole : ∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)),
      ApproxOn K PolyFun (fun z => (z - γ x)⁻¹) := fun x hx =>
    approxOn_polyFun_cauchyKernel_of_isPreconnected_compl hK hconn
      (fun h => hne' x hx _ h rfl)
  exact approxOn_polyFun_edgeCauchyIntegral hK hab hγc hFc hne' hpole

/-- A surviving vertical edge integral is approximable by polynomials on `K`. -/
theorem approxOn_polyFun_gridV (hK : IsCompact K) (hconn : IsPreconnected Kᶜ) (hs : 0 < s)
    (hS : GridSelects S s K) (hmemS : ∀ q : ℤ × ℤ, q ∈ S ↔ SelSquare s Ω R q)
    (hF : AnalyticOnNhd ℂ F Ω) {p : ℤ × ℤ} (hne : vCoeff S p ≠ 0) :
    ApproxOn K PolyFun (fun z => gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2) := by
  classical
  set γ : ℝ → ℂ := fun t => ((s * (p.1 : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I with hγdef
  have hab : s * (p.2 : ℝ) ≤ s * ((p.2 : ℝ) + 1) := by nlinarith
  have hboth : ∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)),
      γ t ∈ gridSquare s p.1 p.2 ∧ γ t ∈ gridSquare s (p.1 - 1) p.2 :=
    fun t ht => vEdgePoint_mem_squares hs p ht
  have hedgeΩ : ∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)), γ t ∈ Ω := by
    intro t ht
    rcases exists_notSelSquare_of_vCoeff_ne hmemS hne with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2.1 (hboth t ht).2
    · exact h1.1 (hboth t ht).1
  have hFc : ContinuousOn F (γ '' Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1))) := by
    rintro w ⟨t, ht, rfl⟩
    exact ((hF _ (hedgeΩ t ht)).continuousAt).continuousWithinAt
  have hγc : ContinuousOn γ (Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1))) := by
    apply Continuous.continuousOn
    rw [hγdef]
    fun_prop
  have hne' : ∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)), ∀ z ∈ K, γ t ≠ z := by
    intro t ht z hz htz
    refine vEdge_avoids_of_vCoeff_ne_zero hs hS hne hz ⟨?_, ?_, ?_⟩
    · rw [← htz, hγdef]; exact cornerPt_re _ _
    · rw [← htz, hγdef]; exact (cornerPt_im _ _).symm ▸ ht.1
    · rw [← htz, hγdef]; exact (cornerPt_im _ _).symm ▸ ht.2
  have hpole : ∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)),
      ApproxOn K PolyFun (fun z => (z - γ t)⁻¹) := fun t ht =>
    approxOn_polyFun_cauchyKernel_of_isPreconnected_compl hK hconn
      (fun h => hne' t ht _ h rfl)
  have hmain := approxOn_polyFun_edgeCauchyIntegral hK hab hγc hFc hne' hpole
  have hfun : (fun z => gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2)
      = fun z => Complex.I * edgeCauchyIntegral F γ (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)) z := by
    funext z
    rfl
  rw [hfun]
  exact approxOn_smul polyFun_smul Complex.I hmain

/-- **The contour functional is approximable by polynomials on `K`.** -/
theorem approxOn_polyFun_contourFunctional (hK : IsCompact K) (hconn : IsPreconnected Kᶜ)
    (hs : 0 < s) (hS : GridSelects S s K) (hmemS : ∀ q : ℤ × ℤ, q ∈ S ↔ SelSquare s Ω R q)
    (hF : AnalyticOnNhd ℂ F Ω) :
    ApproxOn K PolyFun (contourFunctional F s S) := by
  classical
  have hHterm : ∀ p ∈ S ∪ S.image shiftUp,
      ApproxOn K PolyFun (fun z => hCoeff S p * gridH (fun w => F w * (w - z)⁻¹) s p.1 p.2) := by
    intro p _
    by_cases hc : hCoeff S p = 0
    · have hfun : (fun z => hCoeff S p * gridH (fun w => F w * (w - z)⁻¹) s p.1 p.2)
          = fun _ : ℂ => (0 : ℂ) := by
        funext z
        rw [hc, zero_mul]
      rw [hfun]
      exact approxOn_of_mem polyFun_zero
    · exact approxOn_smul polyFun_smul _ (approxOn_polyFun_gridH hK hconn hs hS hmemS hF hc)
  have hVterm : ∀ p ∈ S ∪ S.image shiftRight,
      ApproxOn K PolyFun (fun z => vCoeff S p * gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2) := by
    intro p _
    by_cases hc : vCoeff S p = 0
    · have hfun : (fun z => vCoeff S p * gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2)
          = fun _ : ℂ => (0 : ℂ) := by
        funext z
        rw [hc, zero_mul]
      rw [hfun]
      exact approxOn_of_mem polyFun_zero
    · exact approxOn_smul polyFun_smul _ (approxOn_polyFun_gridV hK hconn hs hS hmemS hF hc)
  have hH := approxOn_finsetSum (K := K) (C := PolyFun) polyFun_zero polyFun_add
    (S ∪ S.image shiftUp) hHterm
  have hV := approxOn_finsetSum (K := K) (C := PolyFun) polyFun_zero polyFun_add
    (S ∪ S.image shiftRight) hVterm
  exact approxOn_add polyFun_add hH hV

/-! ## Continuity of the contour functional on `K` -/

/-- The edge integral of a Cauchy kernel is differentiable away from the edge. -/
theorem differentiableAt_edgeCauchyIntegral {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hFc : ContinuousOn F (γ '' Icc a b)) {z₀ : ℂ}
    (hne : ∀ x ∈ Icc a b, γ x ≠ z₀) :
    DifferentiableAt ℂ (fun z => edgeCauchyIntegral F γ a b z) z₀ := by
  classical
  -- the distance from `z₀` to the edge is positive
  have hne' : (Icc a b).Nonempty := ⟨a, le_refl a, hab⟩
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne'
    (f := fun x => ‖γ x - z₀‖) ((hγ.sub continuousOn_const).norm)
  set δ : ℝ := ‖γ x₀ - z₀‖ with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (hne x₀ hx₀))
  have hsep : ∀ x ∈ Icc a b, δ ≤ ‖γ x - z₀‖ := fun x hx => isMinOn_iff.mp hmin x hx
  -- a bound for `F` on the edge
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hγ).exists_bound_of_continuousOn hFc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM _ ⟨x₀, hx₀, rfl⟩)
  have hdist : ∀ x ∈ Icc a b, ∀ z ∈ ball z₀ (δ / 2), δ / 2 ≤ ‖γ x - z‖ := by
    intro x hx z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := hsep x hx
    have h2 := norm_sub_le_norm_sub_add_norm_sub (γ x) z z₀
    linarith
  have hnz : ∀ x ∈ Icc a b, ∀ z ∈ ball z₀ (δ / 2), γ x - z ≠ 0 := fun x hx z hz =>
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hdist x hx z hz))
  refine _root_.HTGeometry.differentiableAt_intervalIntegral_of_bound
    (F := fun z x => F (γ x) * (γ x - z)⁻¹) hab (by positivity : 0 < δ / 2) ?_ ?_
    (C := M * (δ / 2)⁻¹) ?_
  · intro z hz
    refine (hFc.comp hγ (mapsTo_image _ _)).mul ((hγ.sub continuousOn_const).inv₀ ?_)
    exact fun x hx => hnz x hx z hz
  · intro x hx z hz
    have h1 : DifferentiableAt ℂ (fun z : ℂ => γ x - z) z :=
      (differentiableAt_const _).sub differentiableAt_id
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (γ x - z)⁻¹) z :=
      (differentiableAt_inv (hnz x hx z hz)).comp z h1
    exact ((differentiableAt_const _).mul h2).differentiableWithinAt
  · intro x hx z hz
    rw [norm_mul, norm_inv]
    exact mul_le_mul (hM _ ⟨x, hx, rfl⟩) (inv_anti₀ (by positivity) (hdist x hx z hz))
      (by positivity) hM0

/-- The contour functional is differentiable at every point of `K`. -/
theorem differentiableAt_contourFunctional (hs : 0 < s) (hS : GridSelects S s K)
    (hmemS : ∀ q : ℤ × ℤ, q ∈ S ↔ SelSquare s Ω R q) (hF : AnalyticOnNhd ℂ F Ω) {z₀ : ℂ}
    (hz₀ : z₀ ∈ K) :
    DifferentiableAt ℂ (contourFunctional F s S) z₀ := by
  classical
  have hfun : contourFunctional F s S = fun z =>
      (∑ p ∈ S ∪ S.image shiftUp, hCoeff S p * gridH (fun w => F w * (w - z)⁻¹) s p.1 p.2)
        + ∑ p ∈ S ∪ S.image shiftRight,
          vCoeff S p * gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2 := rfl
  rw [hfun]
  refine DifferentiableAt.add (DifferentiableAt.fun_sum fun p _ => ?_)
    (DifferentiableAt.fun_sum fun p _ => ?_)
  · by_cases hc : hCoeff S p = 0
    · have h0 : (fun z => hCoeff S p * gridH (fun w => F w * (w - z)⁻¹) s p.1 p.2)
          = fun _ : ℂ => (0 : ℂ) := by
        funext z
        rw [hc, zero_mul]
      rw [h0]
      exact differentiableAt_const _
    · refine DifferentiableAt.const_mul ?_ _
      set γ : ℝ → ℂ := fun x => (x : ℂ) + ((s * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I with hγdef
      have hab : s * (p.1 : ℝ) ≤ s * ((p.1 : ℝ) + 1) := by nlinarith
      have hboth : ∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)),
          γ x ∈ gridSquare s p.1 p.2 ∧ γ x ∈ gridSquare s p.1 (p.2 - 1) :=
        fun x hx => hEdgePoint_mem_squares hs p hx
      have hedgeΩ : ∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)), γ x ∈ Ω := by
        intro x hx
        rcases exists_notSelSquare_of_hCoeff_ne hmemS hc with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2.1 (hboth x hx).2
        · exact h1.1 (hboth x hx).1
      have hFc : ContinuousOn F (γ '' Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1))) := by
        rintro w ⟨x, hx, rfl⟩
        exact ((hF _ (hedgeΩ x hx)).continuousAt).continuousWithinAt
      have hγc : ContinuousOn γ (Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1))) := by
        apply Continuous.continuousOn
        rw [hγdef]
        fun_prop
      have hne' : ∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)), γ x ≠ z₀ := by
        intro x hx hxz
        refine hEdge_avoids_of_hCoeff_ne_zero hs hS hc hz₀ ⟨?_, ?_, ?_⟩
        · rw [← hxz, hγdef]; exact (cornerPt_re _ _).symm ▸ hx.1
        · rw [← hxz, hγdef]; exact (cornerPt_re _ _).symm ▸ hx.2
        · rw [← hxz, hγdef]; exact cornerPt_im _ _
      exact differentiableAt_edgeCauchyIntegral hab hγc hFc hne'
  · by_cases hc : vCoeff S p = 0
    · have h0 : (fun z => vCoeff S p * gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2)
          = fun _ : ℂ => (0 : ℂ) := by
        funext z
        rw [hc, zero_mul]
      rw [h0]
      exact differentiableAt_const _
    · refine DifferentiableAt.const_mul ?_ _
      set γ : ℝ → ℂ := fun t => ((s * (p.1 : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I with hγdef
      have hab : s * (p.2 : ℝ) ≤ s * ((p.2 : ℝ) + 1) := by nlinarith
      have hboth : ∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)),
          γ t ∈ gridSquare s p.1 p.2 ∧ γ t ∈ gridSquare s (p.1 - 1) p.2 :=
        fun t ht => vEdgePoint_mem_squares hs p ht
      have hedgeΩ : ∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)), γ t ∈ Ω := by
        intro t ht
        rcases exists_notSelSquare_of_vCoeff_ne hmemS hc with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2.1 (hboth t ht).2
        · exact h1.1 (hboth t ht).1
      have hFc : ContinuousOn F (γ '' Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1))) := by
        rintro w ⟨t, ht, rfl⟩
        exact ((hF _ (hedgeΩ t ht)).continuousAt).continuousWithinAt
      have hγc : ContinuousOn γ (Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1))) := by
        apply Continuous.continuousOn
        rw [hγdef]
        fun_prop
      have hne' : ∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)), γ t ≠ z₀ := by
        intro t ht htz
        refine vEdge_avoids_of_vCoeff_ne_zero hs hS hc hz₀ ⟨?_, ?_, ?_⟩
        · rw [← htz, hγdef]; exact cornerPt_re _ _
        · rw [← htz, hγdef]; exact (cornerPt_im _ _).symm ▸ ht.1
        · rw [← htz, hγdef]; exact (cornerPt_im _ _).symm ▸ ht.2
      have hmain := differentiableAt_edgeCauchyIntegral hab hγc hFc hne'
      have hfun : (fun z => gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2)
          = fun z => Complex.I * edgeCauchyIntegral F γ (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)) z := by
        funext z
        rfl
      rw [hfun]
      exact hmain.const_mul _

/-! ## The contour functional equals `2πi F` on `K` -/

/-- The floor square of a real coordinate. -/
theorem grid_floor_le {x : ℝ} (hs : 0 < s) :
    s * ((⌊x / s⌋ : ℤ) : ℝ) ≤ x ∧ x < s * (((⌊x / s⌋ : ℤ) : ℝ) + 1) := by
  have hfl : ((⌊x / s⌋ : ℤ) : ℝ) ≤ x / s := Int.floor_le (x / s)
  have hfu : x / s < ((⌊x / s⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one (x / s)
  have hkey : s * (x / s) = x := by field_simp
  constructor
  · calc s * ((⌊x / s⌋ : ℤ) : ℝ) ≤ s * (x / s) := by nlinarith
      _ = x := hkey
  · calc x = s * (x / s) := hkey.symm
      _ < s * (((⌊x / s⌋ : ℤ) : ℝ) + 1) := by nlinarith

/-- A coordinate strictly inside a grid cell is off the grid lines and has that cell as floor. -/
theorem grid_cell_of_lt {x : ℝ} {m : ℤ} (hs : 0 < s) (h1 : s * (m : ℝ) < x)
    (h2 : x < s * ((m : ℝ) + 1)) : (∀ k : ℤ, x ≠ s * k) ∧ ⌊x / s⌋ = m := by
  constructor
  · intro k hk
    rw [hk] at h1 h2
    have hk1 : (m : ℝ) < k := lt_of_mul_lt_mul_left h1 hs.le
    have hk2 : (k : ℝ) < (m : ℝ) + 1 := lt_of_mul_lt_mul_left h2 hs.le
    have hk1' : m < k := by exact_mod_cast hk1
    have hk2' : k < m + 1 := by exact_mod_cast hk2
    omega
  · rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hs]
      linarith
    · rw [div_lt_iff₀ hs]
      linarith

/-- **The contour functional is `2πi F` at every point of `K`.** -/
theorem contourFunctional_eq_of_mem (hF : AnalyticOnNhd ℂ F Ω) (hs : 0 < s)
    (hSsub : ∀ p ∈ S, gridSquare s p.1 p.2 ⊆ Ω) (hS : GridSelects S s K)
    (hmemS : ∀ q : ℤ × ℤ, q ∈ S ↔ SelSquare s Ω R q) {z₀ : ℂ} (hz₀ : z₀ ∈ K) :
    contourFunctional F s S z₀ = 2 * Real.pi * Complex.I * F z₀ := by
  classical
  set m : ℤ := ⌊z₀.re / s⌋ with hm
  set n : ℤ := ⌊z₀.im / s⌋ with hn
  obtain ⟨hre₁, hre₂⟩ := grid_floor_le (x := z₀.re) hs
  obtain ⟨him₁, him₂⟩ := grid_floor_le (x := z₀.im) hs
  have hzsq : z₀ ∈ gridSquare s m n := mem_gridSquare.2 ⟨⟨hre₁, hre₂.le⟩, ⟨him₁, him₂.le⟩⟩
  have hmn : (m, n) ∈ S := hS (m, n) ⟨z₀, hzsq, hz₀⟩
  -- the open floor square, on which the identity holds
  set U : Set ℂ := {w | s * (m : ℝ) < w.re ∧ w.re < s * ((m : ℝ) + 1) ∧
    s * (n : ℝ) < w.im ∧ w.im < s * ((n : ℝ) + 1)} with hU
  have hUeq : ∀ w ∈ U, contourFunctional F s S w = 2 * Real.pi * Complex.I * F w := by
    rintro w ⟨h1, h2, h3, h4⟩
    obtain ⟨hre, hfl⟩ := grid_cell_of_lt hs h1 h2
    obtain ⟨him, hfl'⟩ := grid_cell_of_lt hs h3 h4
    exact contourFunctional_eq hF hs hSsub hre him (by rw [hfl, hfl']; exact hmn)
  -- `z₀` lies in the closure of the open square: approach it from the centre
  have hcl : z₀ ∈ closure U := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set c : ℂ := ((s * ((m : ℝ) + 1 / 2) : ℝ) : ℂ) + ((s * ((n : ℝ) + 1 / 2) : ℝ) : ℂ) * Complex.I
      with hc
    have hcre : c.re = s * ((m : ℝ) + 1 / 2) := cornerPt_re _ _
    have hcim : c.im = s * ((n : ℝ) + 1 / 2) := cornerPt_im _ _
    set t : ℝ := min 1 (ε / (‖c - z₀‖ + 1)) with ht
    have htpos : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htε : t * ‖c - z₀‖ < ε := by
      calc t * ‖c - z₀‖ ≤ (ε / (‖c - z₀‖ + 1)) * ‖c - z₀‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg (c - z₀)]
    refine ⟨z₀ + (t : ℂ) * (c - z₀), ?_, ?_⟩
    · have hwre : (z₀ + (t : ℂ) * (c - z₀)).re = z₀.re + t * (c.re - z₀.re) := by
        simp [Complex.add_re, Complex.mul_re, Complex.sub_re]
      have hwim : (z₀ + (t : ℂ) * (c - z₀)).im = z₀.im + t * (c.im - z₀.im) := by
        simp [Complex.add_im, Complex.mul_im, Complex.sub_im]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hwre, hcre]; nlinarith
      · rw [hwre, hcre]; nlinarith
      · rw [hwim, hcim]; nlinarith
      · rw [hwim, hcim]; nlinarith
    · rw [dist_eq_norm, show z₀ - (z₀ + (t : ℂ) * (c - z₀)) = -((t : ℂ) * (c - z₀)) by ring,
        norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le]
      exact htε
  -- both sides are continuous at `z₀`
  haveI : (𝓝[U] z₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hΦ : Tendsto (contourFunctional F s S) (𝓝[U] z₀) (𝓝 (contourFunctional F s S z₀)) :=
    (differentiableAt_contourFunctional hs hS hmemS hF hz₀).continuousAt.continuousWithinAt.tendsto
  have hFz : Tendsto (fun w => 2 * Real.pi * Complex.I * F w) (𝓝[U] z₀)
      (𝓝 (2 * Real.pi * Complex.I * F z₀)) :=
    (continuousAt_const.mul (hF z₀ (hSsub _ hmn hzsq)).continuousAt).continuousWithinAt.tendsto
  have hΦ' : Tendsto (contourFunctional F s S) (𝓝[U] z₀)
      (𝓝 (2 * Real.pi * Complex.I * F z₀)) :=
    hFz.congr' (eventually_nhdsWithin_of_forall fun w hw => (hUeq w hw).symm)
  exact tendsto_nhds_unique hΦ hΦ'

/-! ## Polynomial Runge approximation -/

/-- **Polynomial Runge approximation on a compact set with connected complement.**  If `F` is
analytic on an open set containing the compact `K` and `ℂ \ K` is connected, then `F` is
uniformly approximable on `K` by polynomials. -/
theorem approxOn_polyFun_of_analyticOnNhd (hΩo : IsOpen Ω) (hF : AnalyticOnNhd ℂ F Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hconn : IsPreconnected Kᶜ) :
    ApproxOn K PolyFun F := by
  classical
  obtain ⟨s, R, δ, S, hs, -, -, -, -, -, -, hmemS, hSel⟩ := exists_rungeSelection hΩo hK hKΩ
  have hSsub : ∀ p ∈ S, gridSquare s p.1 p.2 ⊆ Ω := fun p hp => ((hmemS p).1 hp).1
  have hΦapprox : ApproxOn K PolyFun (contourFunctional F s S) :=
    approxOn_polyFun_contourFunctional hK hconn hs hSel hmemS hF
  have hΦeq : ∀ z ∈ K, contourFunctional F s S z = 2 * Real.pi * Complex.I * F z :=
    fun z hz => contourFunctional_eq_of_mem hF hs hSsub hSel hmemS hz
  have hcne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine approxOn_of_approxOn fun ε hε =>
    ⟨fun z => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * contourFunctional F s S z,
      approxOn_smul polyFun_smul _ hΦapprox, fun z hz => ?_⟩
  beta_reduce
  rw [hΦeq z hz, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul, sub_self, norm_zero]
  exact hε.le

/-- The approximation in the form of an explicit polynomial. -/
theorem exists_polynomial_approx_of_analyticOnNhd (hΩo : IsOpen Ω) (hF : AnalyticOnNhd ℂ F Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hconn : IsPreconnected Kᶜ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖F z - P.eval z‖ ≤ ε := by
  obtain ⟨g, ⟨P, rfl⟩, hg⟩ := approxOn_polyFun_of_analyticOnNhd hΩo hF hK hKΩ hconn ε hε
  exact ⟨P, hg⟩

end

end GaloisForLFunctions.HTGeometry
