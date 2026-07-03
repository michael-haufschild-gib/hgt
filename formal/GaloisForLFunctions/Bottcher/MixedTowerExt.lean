/-
# The norm-bounded tower extension (mixed-pair wiring, step B8)

The mixed q62 capstone needs a `c₁` radical tower whose extension domain avoids
`closedBall 0 2 ⊇ K_{c₂}`.  This file builds `Ext` exactly as `exists_tower_ext`, but on the
wedge-slit scaffold arc at a PRESCRIBED slit angle `θs` whose window avoids the critical-value
ball (`exists_slit_center_avoiding_patch` supplies it), and exports the norm floor
`∀ z ∈ Ext, 2 < ‖z‖` piece by piece:

* the section piece `P0` has Green value `> log rlo ≥ G_c(0) + 1/8` — clear of the
  `closedBall 0 2` pinch band from above (`two_lt_norm_of_greenFunctionDyn_gt`);
* the depth-1 scaffold piece is the one Green-critical piece: there the slit avoidance gives
  `‖σ₁ v‖² = ‖S.T v − c‖ > 4` directly;
* every deeper scaffold piece (`log RW ≤ 4·G_c(0) − 1/2`) and every lobe piece
  (`log rb ≤ 2·G_c(0) − 1/4`) has Green value `< G_c(0) − 1/8` — clear from below
  (`two_lt_norm_of_greenFunctionDyn_lt`).

`TowerSection.restrictLo` raises the inner radius of a section so a caller can enforce
`G_c(0) + 1/8 ≤ log rlo` on the deep tower of `exists_tower_deep_of_anchor`.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.BottcherTowerData
import GaloisForLFunctions.Bottcher.GreenBallPinch

open Complex Set Filter Metric Topology

namespace Bottcher

/-- **Raising the inner radius of a tower section.**  All eight invariants restrict to the
sub-annulus. -/
def TowerSection.restrictLo {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {rlo' : ℝ} (hle : rlo ≤ rlo') : TowerSection c rlo' rhi :=
  have hsub : annulusSet rlo' rhi ⊆ annulusSet rlo rhi := fun _ hz =>
    ⟨lt_of_le_of_lt hle hz.1, hz.2⟩
  { T := S.T
    an := S.an.mono hsub
    level := fun w hw => S.level w (hsub hw)
    odd := fun w hw => S.odd w (hsub hw)
    fe := fun w hw hw2 => S.fe w (hsub hw) (hsub hw2)
    inj := S.inj.mono hsub
    dne := fun w hw => S.dne w (hsub hw)
    wind := fun r hr1 hr2 => S.wind r (lt_of_le_of_lt hle hr1) hr2 }

set_option maxHeartbeats 1600000 in
/-- **The norm-bounded extended domain and deep lobe at depth `k`.**  As `exists_tower_ext`,
with the scaffold arc at the prescribed slit angle `θs` whose window avoids the critical-value
ball, and with the extra export `∀ z ∈ Ext, 2 < ‖z‖`. -/
theorem exists_tower_ext_slit {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hrlo : 1 < rlo) (hc100 : (100:ℝ) ≤ ‖c‖)
    (hh1 : 1 ≤ greenFunctionDyn c 0)
    (hlow18 : greenFunctionDyn c 0 + 1/8 ≤ Real.log rlo)
    {ra rb RW : ℝ} (hra : rlo < ra) (hrb : ra < rb) (hrbRW : rb < RW) (hRWR : RW < R₀)
    (hrb14 : Real.log rb ≤ 2 * greenFunctionDyn c 0 - 1/4)
    (hraRW : ra ^ 2 < RW)
    (hRW12 : Real.log RW ≤ 4 * greenFunctionDyn c 0 - 1/2)
    {θs : ℝ} (hθs1 : -Real.pi ≤ θs) (hθs2 : θs ≤ Real.pi)
    (havoid : ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
      S.T v ∉ Metric.closedBall c 4)
    (k : ℕ) :
    ∃ (Ext : Set ℂ) (SL : ℂ → ℂ),
      IsOpen Ext ∧ IsConnected Ext ∧
      S.T '' annulusSet rlo R₀ ⊆ Ext ∧
      (∀ z ∈ Ext, ∃ j : ℕ, j ≤ k ∧ (quadratic c)^[j] z ∈ S.T '' annulusSet rlo R₀) ∧
      (∀ z ∈ Ext, z ∈ S.T '' annulusSet rlo R₀ ∨
        greenFunctionDyn c z < 2 * greenFunctionDyn c 0) ∧
      (∀ z ∈ Ext, 2 < ‖z‖) ∧
      (∀ z ∈ Ext, ∀ n : ℕ, (quadratic c)^[n] z ≠ 0) ∧
      AnalyticOnNhd ℂ SL (annulusSet ra rb) ∧
      (∀ v ∈ annulusSet ra rb, (quadratic c)^[k] (SL v) = S.T v) ∧
      (∀ v ∈ annulusSet ra rb, greenFunctionDyn c (SL v) = Real.log ‖v‖ / 2 ^ k) ∧
      (∀ v ∈ annulusSet ra rb, deriv SL v ≠ 0) ∧
      (∀ v ∈ annulusSet ra rb, SL v ∈ Ext) ∧
      Set.InjOn SL (annulusSet ra rb) := by
  classical
  have hh0 : 0 < greenFunctionDyn c 0 := by linarith
  have hlow : greenFunctionDyn c 0 < Real.log rlo := by linarith
  have hrb2h : Real.log rb < 2 * greenFunctionDyn c 0 := by linarith
  have hRW4h : Real.log RW < 4 * greenFunctionDyn c 0 := by linarith
  have hh18pos : (0:ℝ) < greenFunctionDyn c 0 - 1/8 := by linarith
  -- the wedge-slit scaffold at the prescribed angle
  have hslitne : ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
      S.T v ≠ c := by
    intro v hv heq
    exact havoid v hv (by rw [heq]; exact Metric.mem_closedBall_self (by norm_num))
  obtain ⟨α, β, J₁, J₂, hαeq, hβeq, hαβ, hβα, hαJ₁, hJ₁J₂, hJ₂β, hJ₁dbl, hJ₂dbl, σ, hσ0, hσP,
    hσsq, hσdbl, hσne⟩ :=
    exists_scaffold_chain_window S hrlo hra hraRW hRWR hRW4h hh0 hlow hθs1 hθs2 hslitne
  have havoidA : ∀ v ∈ arcAnnulus ra RW α β, S.T v ∉ Metric.closedBall c 4 := by
    rw [hαeq, hβeq]
    exact havoid
  obtain ⟨SL, hSL0, hSLP, hSLsq, hSLmatch, hSLne⟩ :=
    exists_matched_lobes S hrlo hlow hra hrb hrbRW hRWR hrb2h hαβ hσ0 hσP hσsq
  have hrapos : (0:ℝ) < ra := by linarith
  have hrlopos : (0:ℝ) < rlo := by linarith
  have hraRW' : ra < RW := lt_trans hrb hrbRW
  set A : Set ℂ := arcAnnulus ra RW α β with hAdef
  set B : Set ℂ := annulusSet ra rb with hBdef
  set P0 : Set ℂ := S.T '' annulusSet rlo R₀ with hP0def
  set Pσ : ℕ → Set ℂ := fun j => σ j '' A with hPσdef
  set PL : ℕ → Set ℂ := fun j => SL j '' B with hPLdef
  have hAopen : IsOpen A := isOpen_arcAnnulus _ _ _ _
  have hBopen : IsOpen B := isOpen_annulusSet _ _
  have hAconn : IsConnected A := isConnected_arcAnnulus hrapos hraRW' hαβ
  have hBconn : IsConnected B := isConnected_annulus hrapos hrb
  have hP0open : IsOpen P0 :=
    isOpen_image_of_analytic_dne (isOpen_annulusSet _ _) S.an S.dne
  have hP0conn : IsConnected P0 :=
    (isConnected_annulus hrlopos (by nlinarith [sq_nonneg rlo] :
      rlo < R₀)).image _ (S.an.continuousOn)
  have hPσopen : ∀ j, IsOpen (Pσ j) := fun j =>
    isOpen_image_of_analytic_dne hAopen (hσP j).1 (hσP j).2.2.2.1
  have hPσconn : ∀ j, IsConnected (Pσ j) := fun j =>
    hAconn.image _ ((hσP j).1.continuousOn)
  have hPLopen : ∀ j, IsOpen (PL j) := fun j =>
    isOpen_image_of_analytic_dne hBopen (hSLP j).1 (hSLP j).2.2.2.1
  have hPLconn : ∀ j, IsConnected (PL j) := fun j =>
    hBconn.image _ ((hSLP j).1.continuousOn)
  -- the doubling window is nonempty
  have hrasqrt : ra < Real.sqrt RW := by
    have h1 : Real.sqrt (ra ^ 2) < Real.sqrt RW :=
      Real.sqrt_lt_sqrt (by positivity) hraRW
    rwa [Real.sqrt_sq (le_of_lt hrapos)] at h1
  have hWne : (arcAnnulus ra (Real.sqrt RW) J₁ J₂).Nonempty :=
    (isConnected_arcAnnulus hrapos hrasqrt hJ₁J₂).nonempty
  have hWsubA : arcAnnulus ra (Real.sqrt RW) J₁ J₂ ⊆ A := by
    intro w hw
    have h1 : arcAnnulus ra (Real.sqrt RW) J₁ J₂ ⊆ arcAnnulus ra RW J₁ J₂ :=
      arcAnnulus_mono_radius (Real.sqrt_pos.mpr (by linarith)) (by
        have h2 : Real.sqrt RW < Real.sqrt (RW ^ 2) :=
          Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
        rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ RW)] at h2
        linarith)
    exact arcAnnulus_mono hαJ₁ hJ₂β (h1 hw)
  have hWsq : ∀ w ∈ arcAnnulus ra (Real.sqrt RW) J₁ J₂, w ^ 2 ∈ A := by
    intro w hw
    apply sq_mem_arcAnnulus (r' := ra) (R' := Real.sqrt RW) _ _ hJ₁dbl hJ₂dbl hw
    · linarith [Real.log_pos (show (1:ℝ) < ra from by nlinarith)]
    · rw [show 2 * Real.log (Real.sqrt RW) = Real.log RW from by
        rw [Real.log_sqrt (by linarith : (0:ℝ) ≤ RW)]; ring]
  have hAsubS : ∀ v ∈ A, v ∈ annulusSet rlo R₀ := by
    intro v hv
    have h1 := arcAnnulus_subset α β hrapos hraRW' hv
    exact ⟨lt_trans hra h1.1, lt_trans h1.2 hRWR⟩
  -- pairwise overlaps
  have hover0 : (P0 ∩ Pσ 1).Nonempty := by
    obtain ⟨w, hw⟩ := hWne
    refine ⟨σ 1 (w ^ 2), ?_, ?_⟩
    · have h1 := hσdbl 0 w hw
      rw [h1, hσ0]
      exact ⟨w, hAsubS w (hWsubA hw), rfl⟩
    · exact ⟨w ^ 2, hWsq w hw, rfl⟩
  have hoverσ : ∀ j : ℕ, (Pσ j ∩ Pσ (j+1)).Nonempty := by
    intro j
    obtain ⟨w, hw⟩ := hWne
    refine ⟨σ (j+1) (w ^ 2), ?_, ?_⟩
    · have h1 := hσdbl j w hw
      rw [h1]
      exact ⟨w, hWsubA hw, rfl⟩
    · exact ⟨w ^ 2, hWsq w hw, rfl⟩
  have hCne : (arcAnnulus ra rb α β).Nonempty :=
    (isConnected_arcAnnulus hrapos hrb hαβ).nonempty
  have hCsubB : arcAnnulus ra rb α β ⊆ B := arcAnnulus_subset _ _ hrapos hrb
  have hCsubA : arcAnnulus ra rb α β ⊆ A :=
    arcAnnulus_mono_radius (by linarith) (le_of_lt hrbRW)
  have hoverL : ∀ j : ℕ, (PL j ∩ Pσ j).Nonempty := by
    intro j
    obtain ⟨v, hv⟩ := hCne
    refine ⟨SL j v, ⟨v, hCsubB hv, rfl⟩, ?_⟩
    rw [hSLmatch j v hv]
    exact ⟨v, hCsubA hv, rfl⟩
  have hPσ0sub : Pσ 0 ⊆ P0 := by
    rintro z ⟨v, hv, rfl⟩
    rw [hσ0]
    exact ⟨v, hAsubS v hv, rfl⟩
  have hPL0sub : PL 0 ⊆ P0 := by
    rintro z ⟨v, hv, rfl⟩
    rw [hSL0]
    refine ⟨v, ?_, rfl⟩
    obtain ⟨h1, h2⟩ := hv
    exact ⟨lt_trans hra h1, lt_trans h2 (lt_trans hrbRW hRWR)⟩
  -- the growing union, defined recursively so the recurrence is definitional
  set Conn : ℕ → Set ℂ := fun n =>
    Nat.rec P0 (fun j prev => prev ∪ (Pσ (j+1) ∪ PL (j+1))) n with hConndef
  have hConnsucc : ∀ n : ℕ, Conn (n+1) = Conn n ∪ (Pσ (n+1) ∪ PL (n+1)) := fun n => rfl
  have hP0Conn : ∀ n : ℕ, P0 ⊆ Conn n := by
    intro n
    induction n with
    | zero => exact fun z hz => hz
    | succ n ih =>
        rw [hConnsucc n]
        exact fun z hz => Or.inl (ih hz)
  have hPσConn : ∀ n : ℕ, ∀ j : ℕ, j ≤ n → Pσ j ⊆ Conn n := by
    intro n
    induction n with
    | zero =>
        intro j hj
        interval_cases j
        exact hPσ0sub
    | succ n ih =>
        intro j hj
        rcases Nat.lt_or_ge j (n+1) with hlt | hge
        · rw [hConnsucc n]
          exact fun z hz => Or.inl (ih j (by omega) hz)
        · have hj' : j = n + 1 := by omega
          subst hj'
          rw [hConnsucc n]
          exact fun z hz => Or.inr (Or.inl hz)
  have hPLConn : ∀ n : ℕ, ∀ j : ℕ, j ≤ n → PL j ⊆ Conn n := by
    intro n
    induction n with
    | zero =>
        intro j hj
        interval_cases j
        exact fun z hz => hPL0sub hz
    | succ n ih =>
        intro j hj
        rcases Nat.lt_or_ge j (n+1) with hlt | hge
        · rw [hConnsucc n]
          exact fun z hz => Or.inl (ih j (by omega) hz)
        · have hj' : j = n + 1 := by omega
          subst hj'
          rw [hConnsucc n]
          exact fun z hz => Or.inr (Or.inr hz)
  have hConnConn : ∀ n : ℕ, IsConnected (Conn n) ∧ IsOpen (Conn n) := by
    intro n
    induction n with
    | zero => exact ⟨hP0conn, hP0open⟩
    | succ n ih =>
        obtain ⟨ihc, iho⟩ := ih
        rw [hConnsucc n]
        have hover : ∃ z, z ∈ Conn n ∧ z ∈ Pσ (n+1) := by
          rcases Nat.eq_zero_or_pos n with hn0 | hnpos
          · subst hn0
            obtain ⟨z, hz1, hz2⟩ := hover0
            exact ⟨z, hP0Conn 0 hz1, hz2⟩
          · obtain ⟨z, hz1, hz2⟩ := hoverσ n
            exact ⟨z, hPσConn n n le_rfl hz1, hz2⟩
        have h2 : IsConnected (Pσ (n+1) ∪ PL (n+1)) := by
          obtain ⟨z, hz1, hz2⟩ := hoverL (n+1)
          exact IsConnected.union ⟨z, hz2, hz1⟩ (hPσconn (n+1)) (hPLconn (n+1))
        obtain ⟨z, hz1, hz2⟩ := hover
        refine ⟨IsConnected.union ⟨z, hz1, Or.inl hz2⟩ ihc h2, ?_⟩
        exact iho.union ((hPσopen (n+1)).union (hPLopen (n+1)))
  have hreach : ∀ n : ℕ, ∀ z ∈ Conn n, ∃ j : ℕ, j ≤ n ∧
      (quadratic c)^[j] z ∈ P0 := by
    intro n
    induction n with
    | zero =>
        intro z hz
        exact ⟨0, le_rfl, by simpa using hz⟩
    | succ n ih =>
        intro z hz
        rw [hConnsucc n] at hz
        rcases hz with hz | hz
        · obtain ⟨j, hj, hzj⟩ := ih z hz
          exact ⟨j, by omega, hzj⟩
        · rcases hz with hzσ | hzL
          · obtain ⟨v, hv, rfl⟩ := hzσ
            refine ⟨n+1, le_rfl, ?_⟩
            rw [(hσP (n+1)).2.2.2.2 v hv]
            exact ⟨v, hAsubS v hv, rfl⟩
          · obtain ⟨v, hv, rfl⟩ := hzL
            refine ⟨n+1, le_rfl, ?_⟩
            rw [(hSLP (n+1)).2.2.2.2 v hv]
            refine ⟨v, ?_, rfl⟩
            obtain ⟨h1, h2⟩ := hv
            exact ⟨lt_trans hra h1, lt_trans h2 (lt_trans hrbRW hRWR)⟩
  have hlevels : ∀ n : ℕ, ∀ z ∈ Conn n, z ∈ P0 ∨
      greenFunctionDyn c z < 2 * greenFunctionDyn c 0 := by
    intro n
    induction n with
    | zero =>
        intro z hz
        exact Or.inl hz
    | succ n ih =>
        intro z hz
        rw [hConnsucc n] at hz
        rcases hz with hz | hz
        · exact ih z hz
        · right
          rcases hz with hzσ | hzL
          · obtain ⟨v, hv, rfl⟩ := hzσ
            rw [(hσP (n+1)).2.1 v hv]
            have h1 : Real.log ‖v‖ < Real.log RW := by
              have h2 := (arcAnnulus_subset _ _ hrapos hraRW' hv).2
              exact Real.log_lt_log (lt_trans hrapos
                (arcAnnulus_subset _ _ hrapos hraRW' hv).1) h2
            have h3 : (2:ℝ) ≤ 2 ^ (n+1) := by
              calc (2:ℝ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (n+1) := by
                  apply pow_le_pow_right₀ (by norm_num)
                  omega
            have h4 : (0:ℝ) < Real.log ‖v‖ := by
              have h5 := (arcAnnulus_subset _ _ hrapos hraRW' hv).1
              exact Real.log_pos (lt_trans (by nlinarith : (1:ℝ) < ra) h5)
            rw [div_lt_iff₀ (by positivity)]
            nlinarith
          · obtain ⟨v, hv, rfl⟩ := hzL
            rw [(hSLP (n+1)).2.1 v hv]
            have h1 : Real.log ‖v‖ < Real.log rb :=
              Real.log_lt_log (lt_trans hrapos hv.1) hv.2
            have h3 : (2:ℝ) ≤ 2 ^ (n+1) := by
              calc (2:ℝ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (n+1) := by
                  apply pow_le_pow_right₀ (by norm_num)
                  omega
            have h4 : (0:ℝ) < Real.log ‖v‖ :=
              Real.log_pos (lt_trans (by nlinarith : (1:ℝ) < ra) hv.1)
            rw [div_lt_iff₀ (by positivity)]
            nlinarith
  -- the norm floor, piece by piece
  have hnormAll : ∀ n : ℕ, ∀ z ∈ Conn n, 2 < ‖z‖ := by
    intro n
    induction n with
    | zero =>
        rintro z ⟨v, hv, rfl⟩
        apply two_lt_norm_of_greenFunctionDyn_gt hc100
        rw [S.level v hv]
        have h1 : Real.log rlo < Real.log ‖v‖ := Real.log_lt_log hrlopos hv.1
        linarith
    | succ n ih =>
        intro z hz
        rw [hConnsucc n] at hz
        rcases hz with hz | hz
        · exact ih z hz
        · rcases hz with hzσ | hzL
          · obtain ⟨v, hv, rfl⟩ := hzσ
            rcases Nat.eq_zero_or_pos n with hn0 | hnpos
            · -- depth 1: the slit avoidance gives the norm floor directly
              subst hn0
              have hsq1 : σ 1 v ^ 2 = σ 0 v - c := hσsq 0 v hv
              rw [hσ0] at hsq1
              have h5 := havoidA v hv
              rw [Metric.mem_closedBall, dist_eq_norm] at h5
              have h4 : 4 < ‖S.T v - c‖ := not_le.mp h5
              have hn2 : ‖σ 1 v‖ ^ 2 = ‖S.T v - c‖ := by
                rw [← norm_pow, hsq1]
              nlinarith [norm_nonneg (σ 1 v)]
            · -- depth ≥ 2: Green value below `4·(G_c(0) − 1/8) / 4`
              apply two_lt_norm_of_greenFunctionDyn_lt hc100
              rw [(hσP (n+1)).2.1 v hv]
              have h1 : Real.log ‖v‖ < Real.log RW := by
                have h2 := (arcAnnulus_subset _ _ hrapos hraRW' hv).2
                exact Real.log_lt_log (lt_trans hrapos
                  (arcAnnulus_subset _ _ hrapos hraRW' hv).1) h2
              have h3 : (4:ℝ) ≤ 2 ^ (n+1) := by
                calc (4:ℝ) = 2 ^ 2 := by norm_num
                  _ ≤ 2 ^ (n+1) := by
                    apply pow_le_pow_right₀ (by norm_num)
                    omega
              rw [div_lt_iff₀ (by positivity)]
              nlinarith [hh18pos]
          · -- lobes: Green value below `2·(G_c(0) − 1/8) / 2`
            obtain ⟨v, hv, rfl⟩ := hzL
            apply two_lt_norm_of_greenFunctionDyn_lt hc100
            rw [(hSLP (n+1)).2.1 v hv]
            have h1 : Real.log ‖v‖ < Real.log rb :=
              Real.log_lt_log (lt_trans hrapos hv.1) hv.2
            have h3 : (2:ℝ) ≤ 2 ^ (n+1) := by
              calc (2:ℝ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (n+1) := by
                  apply pow_le_pow_right₀ (by norm_num)
                  omega
            rw [div_lt_iff₀ (by positivity)]
            nlinarith [hh18pos]
  -- forward orbits of section values never vanish: level argument above depth, chain below
  have hne_of_level : ∀ w : ℂ, greenFunctionDyn c 0 < greenFunctionDyn c w → w ≠ 0 := by
    intro w hG h0
    rw [h0] at hG
    exact lt_irrefl _ hG
  have hT_orbit : ∀ w ∈ annulusSet rlo R₀, ∀ n : ℕ, (quadratic c)^[n] (S.T w) ≠ 0 := by
    intro w hw n
    apply hne_of_level
    rw [greenFunctionDyn_iterate, S.level w hw]
    have h1 : Real.log rlo < Real.log ‖w‖ := Real.log_lt_log (by linarith) hw.1
    have h2 : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith [hlow]
  have hσ_fiter : ∀ n j : ℕ, n ≤ j → ∀ v ∈ arcAnnulus ra RW α β,
      (quadratic c)^[n] (σ j v) = σ (j - n) v := by
    intro n
    induction n with
    | zero =>
        intro j _ v _
        simp
    | succ m ih =>
        intro j hmj v hv
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hlink : quadratic c (σ (j' + 1) v) = σ j' v := by
          have h1 := hσsq j' v hv
          unfold quadratic
          rw [h1]
          ring
        rw [Function.iterate_succ_apply, hlink]
        rw [ih j' (by omega) v hv]
        congr 1
        omega
  have hSL_fiter : ∀ n j : ℕ, n ≤ j → ∀ v ∈ annulusSet ra rb,
      (quadratic c)^[n] (SL j v) = SL (j - n) v := by
    intro n
    induction n with
    | zero =>
        intro j _ v _
        simp
    | succ m ih =>
        intro j hmj v hv
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hlink : quadratic c (SL (j' + 1) v) = SL j' v := by
          have h1 := hSLsq j' v hv
          unfold quadratic
          rw [h1]
          ring
        rw [Function.iterate_succ_apply, hlink]
        rw [ih j' (by omega) v hv]
        congr 1
        omega
  have horb : ∀ nn : ℕ, ∀ z ∈ Conn nn, ∀ n : ℕ, (quadratic c)^[n] z ≠ 0 := by
    intro nn
    induction nn with
    | zero =>
        rintro z hz n
        obtain ⟨w, hw, rfl⟩ := hz
        exact hT_orbit w hw n
    | succ m ih =>
        intro z hz n
        rw [hConnsucc m] at hz
        rcases hz with hz | hz
        · exact ih z hz n
        · rcases hz with hzσ | hzL
          · obtain ⟨v, hv, rfl⟩ := hzσ
            rcases le_or_gt n (m+1) with hn | hn
            · rw [hσ_fiter n (m+1) hn v hv]
              exact hσne (m+1-n) v hv
            · have h1 : (quadratic c)^[n] (σ (m+1) v)
                  = (quadratic c)^[n - (m+1)] ((quadratic c)^[m+1] (σ (m+1) v)) := by
                rw [← Function.iterate_add_apply]
                congr 1
                omega
              rw [h1, (hσP (m+1)).2.2.2.2 v hv]
              exact hT_orbit v (hAsubS v hv) (n - (m+1))
          · obtain ⟨v, hv, rfl⟩ := hzL
            rcases le_or_gt n (m+1) with hn | hn
            · rw [hSL_fiter n (m+1) hn v hv]
              exact hSLne (m+1-n) v hv
            · have h1 : (quadratic c)^[n] (SL (m+1) v)
                  = (quadratic c)^[n - (m+1)] ((quadratic c)^[m+1] (SL (m+1) v)) := by
                rw [← Function.iterate_add_apply]
                congr 1
                omega
              rw [h1, (hSLP (m+1)).2.2.2.2 v hv]
              apply hT_orbit v _ (n - (m+1))
              obtain ⟨h2, h3⟩ := hv
              exact ⟨lt_trans hra h2, lt_trans h3 (lt_trans hrbRW hRWR)⟩
  refine ⟨Conn k, SL k, (hConnConn k).2, (hConnConn k).1, hP0Conn k, hreach k, hlevels k,
    hnormAll k, horb k, (hSLP k).1, (hSLP k).2.2.2.2, (hSLP k).2.1, (hSLP k).2.2.2.1, ?_,
    (hSLP k).2.2.1⟩
  intro v hv
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact hPL0sub ⟨v, hv, rfl⟩
  · exact hPLConn k k le_rfl ⟨v, hv, rfl⟩

end Bottcher

namespace Bottcher

set_option maxHeartbeats 1600000 in
/-- **The `s`-norm-bounded extended domain and deep lobe at depth `k`.**  As
`exists_tower_ext_slit`, with the avoided critical-value ball freed to radius `s²`
(`2 ≤ s`, `s² ≤ ‖c‖/40`) and the norm floor raised to `∀ z ∈ Ext, s < ‖z‖`. -/
theorem exists_tower_ext_slit_s {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hrlo : 1 < rlo) (hc100 : (100:ℝ) ≤ ‖c‖)
    (hh1 : 1 ≤ greenFunctionDyn c 0)
    (hlow18 : greenFunctionDyn c 0 + 1/8 ≤ Real.log rlo)
    {ra rb RW : ℝ} (hra : rlo < ra) (hrb : ra < rb) (hrbRW : rb < RW) (hRWR : RW < R₀)
    (hrb14 : Real.log rb ≤ 2 * greenFunctionDyn c 0 - 1/4)
    (hraRW : ra ^ 2 < RW)
    (hRW12 : Real.log RW ≤ 4 * greenFunctionDyn c 0 - 1/2)
    {s : ℝ} (hs2 : 2 ≤ s) (hs40 : s ^ 2 ≤ ‖c‖ / 40)
    {θs : ℝ} (hθs1 : -Real.pi ≤ θs) (hθs2 : θs ≤ Real.pi)
    (havoid : ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
      S.T v ∉ Metric.closedBall c (s ^ 2))
    (k : ℕ) :
    ∃ (Ext : Set ℂ) (SL : ℂ → ℂ),
      IsOpen Ext ∧ IsConnected Ext ∧
      S.T '' annulusSet rlo R₀ ⊆ Ext ∧
      (∀ z ∈ Ext, ∃ j : ℕ, j ≤ k ∧ (quadratic c)^[j] z ∈ S.T '' annulusSet rlo R₀) ∧
      (∀ z ∈ Ext, z ∈ S.T '' annulusSet rlo R₀ ∨
        greenFunctionDyn c z < 2 * greenFunctionDyn c 0) ∧
      (∀ z ∈ Ext, s < ‖z‖) ∧
      (∀ z ∈ Ext, ∀ n : ℕ, (quadratic c)^[n] z ≠ 0) ∧
      AnalyticOnNhd ℂ SL (annulusSet ra rb) ∧
      (∀ v ∈ annulusSet ra rb, (quadratic c)^[k] (SL v) = S.T v) ∧
      (∀ v ∈ annulusSet ra rb, greenFunctionDyn c (SL v) = Real.log ‖v‖ / 2 ^ k) ∧
      (∀ v ∈ annulusSet ra rb, deriv SL v ≠ 0) ∧
      (∀ v ∈ annulusSet ra rb, SL v ∈ Ext) ∧
      Set.InjOn SL (annulusSet ra rb) := by
  classical
  have hh0 : 0 < greenFunctionDyn c 0 := by linarith
  have hlow : greenFunctionDyn c 0 < Real.log rlo := by linarith
  have hrb2h : Real.log rb < 2 * greenFunctionDyn c 0 := by linarith
  have hRW4h : Real.log RW < 4 * greenFunctionDyn c 0 := by linarith
  have hh18pos : (0:ℝ) < greenFunctionDyn c 0 - 1/8 := by linarith
  -- the wedge-slit scaffold at the prescribed angle
  have hslitne : ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
      S.T v ≠ c := by
    intro v hv heq
    exact havoid v hv (by rw [heq]; exact Metric.mem_closedBall_self (by positivity))
  obtain ⟨α, β, J₁, J₂, hαeq, hβeq, hαβ, hβα, hαJ₁, hJ₁J₂, hJ₂β, hJ₁dbl, hJ₂dbl, σ, hσ0, hσP,
    hσsq, hσdbl, hσne⟩ :=
    exists_scaffold_chain_window S hrlo hra hraRW hRWR hRW4h hh0 hlow hθs1 hθs2 hslitne
  have havoidA : ∀ v ∈ arcAnnulus ra RW α β, S.T v ∉ Metric.closedBall c (s ^ 2) := by
    rw [hαeq, hβeq]
    exact havoid
  obtain ⟨SL, hSL0, hSLP, hSLsq, hSLmatch, hSLne⟩ :=
    exists_matched_lobes S hrlo hlow hra hrb hrbRW hRWR hrb2h hαβ hσ0 hσP hσsq
  have hrapos : (0:ℝ) < ra := by linarith
  have hrlopos : (0:ℝ) < rlo := by linarith
  have hraRW' : ra < RW := lt_trans hrb hrbRW
  set A : Set ℂ := arcAnnulus ra RW α β with hAdef
  set B : Set ℂ := annulusSet ra rb with hBdef
  set P0 : Set ℂ := S.T '' annulusSet rlo R₀ with hP0def
  set Pσ : ℕ → Set ℂ := fun j => σ j '' A with hPσdef
  set PL : ℕ → Set ℂ := fun j => SL j '' B with hPLdef
  have hAopen : IsOpen A := isOpen_arcAnnulus _ _ _ _
  have hBopen : IsOpen B := isOpen_annulusSet _ _
  have hAconn : IsConnected A := isConnected_arcAnnulus hrapos hraRW' hαβ
  have hBconn : IsConnected B := isConnected_annulus hrapos hrb
  have hP0open : IsOpen P0 :=
    isOpen_image_of_analytic_dne (isOpen_annulusSet _ _) S.an S.dne
  have hP0conn : IsConnected P0 :=
    (isConnected_annulus hrlopos (by nlinarith [sq_nonneg rlo] :
      rlo < R₀)).image _ (S.an.continuousOn)
  have hPσopen : ∀ j, IsOpen (Pσ j) := fun j =>
    isOpen_image_of_analytic_dne hAopen (hσP j).1 (hσP j).2.2.2.1
  have hPσconn : ∀ j, IsConnected (Pσ j) := fun j =>
    hAconn.image _ ((hσP j).1.continuousOn)
  have hPLopen : ∀ j, IsOpen (PL j) := fun j =>
    isOpen_image_of_analytic_dne hBopen (hSLP j).1 (hSLP j).2.2.2.1
  have hPLconn : ∀ j, IsConnected (PL j) := fun j =>
    hBconn.image _ ((hSLP j).1.continuousOn)
  -- the doubling window is nonempty
  have hrasqrt : ra < Real.sqrt RW := by
    have h1 : Real.sqrt (ra ^ 2) < Real.sqrt RW :=
      Real.sqrt_lt_sqrt (by positivity) hraRW
    rwa [Real.sqrt_sq (le_of_lt hrapos)] at h1
  have hWne : (arcAnnulus ra (Real.sqrt RW) J₁ J₂).Nonempty :=
    (isConnected_arcAnnulus hrapos hrasqrt hJ₁J₂).nonempty
  have hWsubA : arcAnnulus ra (Real.sqrt RW) J₁ J₂ ⊆ A := by
    intro w hw
    have h1 : arcAnnulus ra (Real.sqrt RW) J₁ J₂ ⊆ arcAnnulus ra RW J₁ J₂ :=
      arcAnnulus_mono_radius (Real.sqrt_pos.mpr (by linarith)) (by
        have h2 : Real.sqrt RW < Real.sqrt (RW ^ 2) :=
          Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
        rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ RW)] at h2
        linarith)
    exact arcAnnulus_mono hαJ₁ hJ₂β (h1 hw)
  have hWsq : ∀ w ∈ arcAnnulus ra (Real.sqrt RW) J₁ J₂, w ^ 2 ∈ A := by
    intro w hw
    apply sq_mem_arcAnnulus (r' := ra) (R' := Real.sqrt RW) _ _ hJ₁dbl hJ₂dbl hw
    · linarith [Real.log_pos (show (1:ℝ) < ra from by nlinarith)]
    · rw [show 2 * Real.log (Real.sqrt RW) = Real.log RW from by
        rw [Real.log_sqrt (by linarith : (0:ℝ) ≤ RW)]; ring]
  have hAsubS : ∀ v ∈ A, v ∈ annulusSet rlo R₀ := by
    intro v hv
    have h1 := arcAnnulus_subset α β hrapos hraRW' hv
    exact ⟨lt_trans hra h1.1, lt_trans h1.2 hRWR⟩
  -- pairwise overlaps
  have hover0 : (P0 ∩ Pσ 1).Nonempty := by
    obtain ⟨w, hw⟩ := hWne
    refine ⟨σ 1 (w ^ 2), ?_, ?_⟩
    · have h1 := hσdbl 0 w hw
      rw [h1, hσ0]
      exact ⟨w, hAsubS w (hWsubA hw), rfl⟩
    · exact ⟨w ^ 2, hWsq w hw, rfl⟩
  have hoverσ : ∀ j : ℕ, (Pσ j ∩ Pσ (j+1)).Nonempty := by
    intro j
    obtain ⟨w, hw⟩ := hWne
    refine ⟨σ (j+1) (w ^ 2), ?_, ?_⟩
    · have h1 := hσdbl j w hw
      rw [h1]
      exact ⟨w, hWsubA hw, rfl⟩
    · exact ⟨w ^ 2, hWsq w hw, rfl⟩
  have hCne : (arcAnnulus ra rb α β).Nonempty :=
    (isConnected_arcAnnulus hrapos hrb hαβ).nonempty
  have hCsubB : arcAnnulus ra rb α β ⊆ B := arcAnnulus_subset _ _ hrapos hrb
  have hCsubA : arcAnnulus ra rb α β ⊆ A :=
    arcAnnulus_mono_radius (by linarith) (le_of_lt hrbRW)
  have hoverL : ∀ j : ℕ, (PL j ∩ Pσ j).Nonempty := by
    intro j
    obtain ⟨v, hv⟩ := hCne
    refine ⟨SL j v, ⟨v, hCsubB hv, rfl⟩, ?_⟩
    rw [hSLmatch j v hv]
    exact ⟨v, hCsubA hv, rfl⟩
  have hPσ0sub : Pσ 0 ⊆ P0 := by
    rintro z ⟨v, hv, rfl⟩
    rw [hσ0]
    exact ⟨v, hAsubS v hv, rfl⟩
  have hPL0sub : PL 0 ⊆ P0 := by
    rintro z ⟨v, hv, rfl⟩
    rw [hSL0]
    refine ⟨v, ?_, rfl⟩
    obtain ⟨h1, h2⟩ := hv
    exact ⟨lt_trans hra h1, lt_trans h2 (lt_trans hrbRW hRWR)⟩
  -- the growing union, defined recursively so the recurrence is definitional
  set Conn : ℕ → Set ℂ := fun n =>
    Nat.rec P0 (fun j prev => prev ∪ (Pσ (j+1) ∪ PL (j+1))) n with hConndef
  have hConnsucc : ∀ n : ℕ, Conn (n+1) = Conn n ∪ (Pσ (n+1) ∪ PL (n+1)) := fun n => rfl
  have hP0Conn : ∀ n : ℕ, P0 ⊆ Conn n := by
    intro n
    induction n with
    | zero => exact fun z hz => hz
    | succ n ih =>
        rw [hConnsucc n]
        exact fun z hz => Or.inl (ih hz)
  have hPσConn : ∀ n : ℕ, ∀ j : ℕ, j ≤ n → Pσ j ⊆ Conn n := by
    intro n
    induction n with
    | zero =>
        intro j hj
        interval_cases j
        exact hPσ0sub
    | succ n ih =>
        intro j hj
        rcases Nat.lt_or_ge j (n+1) with hlt | hge
        · rw [hConnsucc n]
          exact fun z hz => Or.inl (ih j (by omega) hz)
        · have hj' : j = n + 1 := by omega
          subst hj'
          rw [hConnsucc n]
          exact fun z hz => Or.inr (Or.inl hz)
  have hPLConn : ∀ n : ℕ, ∀ j : ℕ, j ≤ n → PL j ⊆ Conn n := by
    intro n
    induction n with
    | zero =>
        intro j hj
        interval_cases j
        exact fun z hz => hPL0sub hz
    | succ n ih =>
        intro j hj
        rcases Nat.lt_or_ge j (n+1) with hlt | hge
        · rw [hConnsucc n]
          exact fun z hz => Or.inl (ih j (by omega) hz)
        · have hj' : j = n + 1 := by omega
          subst hj'
          rw [hConnsucc n]
          exact fun z hz => Or.inr (Or.inr hz)
  have hConnConn : ∀ n : ℕ, IsConnected (Conn n) ∧ IsOpen (Conn n) := by
    intro n
    induction n with
    | zero => exact ⟨hP0conn, hP0open⟩
    | succ n ih =>
        obtain ⟨ihc, iho⟩ := ih
        rw [hConnsucc n]
        have hover : ∃ z, z ∈ Conn n ∧ z ∈ Pσ (n+1) := by
          rcases Nat.eq_zero_or_pos n with hn0 | hnpos
          · subst hn0
            obtain ⟨z, hz1, hz2⟩ := hover0
            exact ⟨z, hP0Conn 0 hz1, hz2⟩
          · obtain ⟨z, hz1, hz2⟩ := hoverσ n
            exact ⟨z, hPσConn n n le_rfl hz1, hz2⟩
        have h2 : IsConnected (Pσ (n+1) ∪ PL (n+1)) := by
          obtain ⟨z, hz1, hz2⟩ := hoverL (n+1)
          exact IsConnected.union ⟨z, hz2, hz1⟩ (hPσconn (n+1)) (hPLconn (n+1))
        obtain ⟨z, hz1, hz2⟩ := hover
        refine ⟨IsConnected.union ⟨z, hz1, Or.inl hz2⟩ ihc h2, ?_⟩
        exact iho.union ((hPσopen (n+1)).union (hPLopen (n+1)))
  have hreach : ∀ n : ℕ, ∀ z ∈ Conn n, ∃ j : ℕ, j ≤ n ∧
      (quadratic c)^[j] z ∈ P0 := by
    intro n
    induction n with
    | zero =>
        intro z hz
        exact ⟨0, le_rfl, by simpa using hz⟩
    | succ n ih =>
        intro z hz
        rw [hConnsucc n] at hz
        rcases hz with hz | hz
        · obtain ⟨j, hj, hzj⟩ := ih z hz
          exact ⟨j, by omega, hzj⟩
        · rcases hz with hzσ | hzL
          · obtain ⟨v, hv, rfl⟩ := hzσ
            refine ⟨n+1, le_rfl, ?_⟩
            rw [(hσP (n+1)).2.2.2.2 v hv]
            exact ⟨v, hAsubS v hv, rfl⟩
          · obtain ⟨v, hv, rfl⟩ := hzL
            refine ⟨n+1, le_rfl, ?_⟩
            rw [(hSLP (n+1)).2.2.2.2 v hv]
            refine ⟨v, ?_, rfl⟩
            obtain ⟨h1, h2⟩ := hv
            exact ⟨lt_trans hra h1, lt_trans h2 (lt_trans hrbRW hRWR)⟩
  have hlevels : ∀ n : ℕ, ∀ z ∈ Conn n, z ∈ P0 ∨
      greenFunctionDyn c z < 2 * greenFunctionDyn c 0 := by
    intro n
    induction n with
    | zero =>
        intro z hz
        exact Or.inl hz
    | succ n ih =>
        intro z hz
        rw [hConnsucc n] at hz
        rcases hz with hz | hz
        · exact ih z hz
        · right
          rcases hz with hzσ | hzL
          · obtain ⟨v, hv, rfl⟩ := hzσ
            rw [(hσP (n+1)).2.1 v hv]
            have h1 : Real.log ‖v‖ < Real.log RW := by
              have h2 := (arcAnnulus_subset _ _ hrapos hraRW' hv).2
              exact Real.log_lt_log (lt_trans hrapos
                (arcAnnulus_subset _ _ hrapos hraRW' hv).1) h2
            have h3 : (2:ℝ) ≤ 2 ^ (n+1) := by
              calc (2:ℝ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (n+1) := by
                  apply pow_le_pow_right₀ (by norm_num)
                  omega
            have h4 : (0:ℝ) < Real.log ‖v‖ := by
              have h5 := (arcAnnulus_subset _ _ hrapos hraRW' hv).1
              exact Real.log_pos (lt_trans (by nlinarith : (1:ℝ) < ra) h5)
            rw [div_lt_iff₀ (by positivity)]
            nlinarith
          · obtain ⟨v, hv, rfl⟩ := hzL
            rw [(hSLP (n+1)).2.1 v hv]
            have h1 : Real.log ‖v‖ < Real.log rb :=
              Real.log_lt_log (lt_trans hrapos hv.1) hv.2
            have h3 : (2:ℝ) ≤ 2 ^ (n+1) := by
              calc (2:ℝ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (n+1) := by
                  apply pow_le_pow_right₀ (by norm_num)
                  omega
            have h4 : (0:ℝ) < Real.log ‖v‖ :=
              Real.log_pos (lt_trans (by nlinarith : (1:ℝ) < ra) hv.1)
            rw [div_lt_iff₀ (by positivity)]
            nlinarith
  -- the norm floor, piece by piece
  have hnormAll : ∀ n : ℕ, ∀ z ∈ Conn n, s < ‖z‖ := by
    intro n
    induction n with
    | zero =>
        rintro z ⟨v, hv, rfl⟩
        apply lt_norm_of_greenFunctionDyn_gt_s hc100 hs40
        rw [S.level v hv]
        have h1 : Real.log rlo < Real.log ‖v‖ := Real.log_lt_log hrlopos hv.1
        linarith
    | succ n ih =>
        intro z hz
        rw [hConnsucc n] at hz
        rcases hz with hz | hz
        · exact ih z hz
        · rcases hz with hzσ | hzL
          · obtain ⟨v, hv, rfl⟩ := hzσ
            rcases Nat.eq_zero_or_pos n with hn0 | hnpos
            · -- depth 1: the slit avoidance gives the norm floor directly
              subst hn0
              have hsq1 : σ 1 v ^ 2 = σ 0 v - c := hσsq 0 v hv
              rw [hσ0] at hsq1
              have h5 := havoidA v hv
              rw [Metric.mem_closedBall, dist_eq_norm] at h5
              have h4 : s ^ 2 < ‖S.T v - c‖ := not_le.mp h5
              have hn2 : ‖σ 1 v‖ ^ 2 = ‖S.T v - c‖ := by
                rw [← norm_pow, hsq1]
              nlinarith [norm_nonneg (σ 1 v), hs2]
            · -- depth ≥ 2: Green value below `4·(G_c(0) − 1/8) / 4`
              apply lt_norm_of_greenFunctionDyn_lt_s hc100 hs40
              rw [(hσP (n+1)).2.1 v hv]
              have h1 : Real.log ‖v‖ < Real.log RW := by
                have h2 := (arcAnnulus_subset _ _ hrapos hraRW' hv).2
                exact Real.log_lt_log (lt_trans hrapos
                  (arcAnnulus_subset _ _ hrapos hraRW' hv).1) h2
              have h3 : (4:ℝ) ≤ 2 ^ (n+1) := by
                calc (4:ℝ) = 2 ^ 2 := by norm_num
                  _ ≤ 2 ^ (n+1) := by
                    apply pow_le_pow_right₀ (by norm_num)
                    omega
              rw [div_lt_iff₀ (by positivity)]
              nlinarith [hh18pos]
          · -- lobes: Green value below `2·(G_c(0) − 1/8) / 2`
            obtain ⟨v, hv, rfl⟩ := hzL
            apply lt_norm_of_greenFunctionDyn_lt_s hc100 hs40
            rw [(hSLP (n+1)).2.1 v hv]
            have h1 : Real.log ‖v‖ < Real.log rb :=
              Real.log_lt_log (lt_trans hrapos hv.1) hv.2
            have h3 : (2:ℝ) ≤ 2 ^ (n+1) := by
              calc (2:ℝ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (n+1) := by
                  apply pow_le_pow_right₀ (by norm_num)
                  omega
            rw [div_lt_iff₀ (by positivity)]
            nlinarith [hh18pos]
  -- forward orbits of section values never vanish: level argument above depth, chain below
  have hne_of_level : ∀ w : ℂ, greenFunctionDyn c 0 < greenFunctionDyn c w → w ≠ 0 := by
    intro w hG h0
    rw [h0] at hG
    exact lt_irrefl _ hG
  have hT_orbit : ∀ w ∈ annulusSet rlo R₀, ∀ n : ℕ, (quadratic c)^[n] (S.T w) ≠ 0 := by
    intro w hw n
    apply hne_of_level
    rw [greenFunctionDyn_iterate, S.level w hw]
    have h1 : Real.log rlo < Real.log ‖w‖ := Real.log_lt_log (by linarith) hw.1
    have h2 : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith [hlow]
  have hσ_fiter : ∀ n j : ℕ, n ≤ j → ∀ v ∈ arcAnnulus ra RW α β,
      (quadratic c)^[n] (σ j v) = σ (j - n) v := by
    intro n
    induction n with
    | zero =>
        intro j _ v _
        simp
    | succ m ih =>
        intro j hmj v hv
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hlink : quadratic c (σ (j' + 1) v) = σ j' v := by
          have h1 := hσsq j' v hv
          unfold quadratic
          rw [h1]
          ring
        rw [Function.iterate_succ_apply, hlink]
        rw [ih j' (by omega) v hv]
        congr 1
        omega
  have hSL_fiter : ∀ n j : ℕ, n ≤ j → ∀ v ∈ annulusSet ra rb,
      (quadratic c)^[n] (SL j v) = SL (j - n) v := by
    intro n
    induction n with
    | zero =>
        intro j _ v _
        simp
    | succ m ih =>
        intro j hmj v hv
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hlink : quadratic c (SL (j' + 1) v) = SL j' v := by
          have h1 := hSLsq j' v hv
          unfold quadratic
          rw [h1]
          ring
        rw [Function.iterate_succ_apply, hlink]
        rw [ih j' (by omega) v hv]
        congr 1
        omega
  have horb : ∀ nn : ℕ, ∀ z ∈ Conn nn, ∀ n : ℕ, (quadratic c)^[n] z ≠ 0 := by
    intro nn
    induction nn with
    | zero =>
        rintro z hz n
        obtain ⟨w, hw, rfl⟩ := hz
        exact hT_orbit w hw n
    | succ m ih =>
        intro z hz n
        rw [hConnsucc m] at hz
        rcases hz with hz | hz
        · exact ih z hz n
        · rcases hz with hzσ | hzL
          · obtain ⟨v, hv, rfl⟩ := hzσ
            rcases le_or_gt n (m+1) with hn | hn
            · rw [hσ_fiter n (m+1) hn v hv]
              exact hσne (m+1-n) v hv
            · have h1 : (quadratic c)^[n] (σ (m+1) v)
                  = (quadratic c)^[n - (m+1)] ((quadratic c)^[m+1] (σ (m+1) v)) := by
                rw [← Function.iterate_add_apply]
                congr 1
                omega
              rw [h1, (hσP (m+1)).2.2.2.2 v hv]
              exact hT_orbit v (hAsubS v hv) (n - (m+1))
          · obtain ⟨v, hv, rfl⟩ := hzL
            rcases le_or_gt n (m+1) with hn | hn
            · rw [hSL_fiter n (m+1) hn v hv]
              exact hSLne (m+1-n) v hv
            · have h1 : (quadratic c)^[n] (SL (m+1) v)
                  = (quadratic c)^[n - (m+1)] ((quadratic c)^[m+1] (SL (m+1) v)) := by
                rw [← Function.iterate_add_apply]
                congr 1
                omega
              rw [h1, (hSLP (m+1)).2.2.2.2 v hv]
              apply hT_orbit v _ (n - (m+1))
              obtain ⟨h2, h3⟩ := hv
              exact ⟨lt_trans hra h2, lt_trans h3 (lt_trans hrbRW hRWR)⟩
  refine ⟨Conn k, SL k, (hConnConn k).2, (hConnConn k).1, hP0Conn k, hreach k, hlevels k,
    hnormAll k, horb k, (hSLP k).1, (hSLP k).2.2.2.2, (hSLP k).2.1, (hSLP k).2.2.2.1, ?_,
    (hSLP k).2.2.1⟩
  intro v hv
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact hPL0sub ⟨v, hv, rfl⟩
  · exact hPLConn k k le_rfl ⟨v, hv, rfl⟩

end Bottcher
