#import "@preview/minimal-note:0.10.0": *
#import "@preview/curryst:0.5.1": rule, prooftree
#import "@preview/lemmify:0.1.8": *

#let (
  theorem, lemma, corollary,
  remark, proposition, example,
  proof, rules: thm-rules
) = default-theorems("thm-group", lang: "en")

#show: thm-rules

#show: style-algorithm

#show: minimal-note.with(
  title: [Covalence Design and Implementation],
  author: [Jad Elkhaleq Ghalayini],
  date: "July 2025"
)


= Core Calculus

We begin by giving the core calculus for the `covalence` kernel, as formalized in Lean 4. 
This is a variant of extensional Martin-Löf Type Theory (MLTT) based on a single judgement,
$Γ ⊢ a ≡ b : A$, which reads "$a$ is equal to $b$ at type $A$ in context $Γ$." The rules and
grammar given below correspond to those in the formalization, which is in the 
locally-nameless style #cite(<chargueraud-locally-nameless-2012>).

// TODO: add universe annotations to projections, _or_ remove them in formalization 
// (might be feasible)

#let isok(cx) = $cx sans("ok")$
#let srfl = $sans("rfl")$
#let eqa(ty) = $attach(=, br: ty)$
#let site(d, A, l, r) = $sans("ite")(#d, #A, #l, #r)$
#let sapp(ℓ, A, B, f, a) = $sans("app")_(#ℓ #A . #B)(#f, #a)$
#let sabs(ℓ, A, B, b) = $λ_#ℓ #A . (#b : #B)$
#let smk(ℓ, A, B, a, b) = $sans("mk")_(#ℓ #A . #B)(#a, #b)$
#let ssucc = $sans("s")$
#let natrec(C, n, z, s) = $sans("rec")_ℕ (#C, #n, #z, #s)$
#let wk0(a) = $#a^↑$
#let ulift(A, ℓ) = $#A^(attach(↑, br: #ℓ))$
#let slet(A, a, b) = $sans("let")(#A, #a, #b)$
#let blet(A, a, b) = $sans("let")'(#A, #a, #b)$
#let imax(m, n) = $sans("imax")(m, n)$

#let tfv(tm) = $sans("fv")(tm)$
#let tbv(tm) = $sans("bv")(tm)$

== Grammar

#table(
  columns: 2,
  stroke: none,
  gutter: 2em,
  [
    Terms $a, A, φ$ consist of:
    / Variables: $x$
    / Universes: $cal(U)_ℓ$ parametrized by a _level_ $ℓ ∈ ℕ$
    / Unit and empty types: $bold(1)_ℓ, *_ℓ, bold(0)_ℓ$
    / Equations: $a eqa(A) b$
    / Dependent functions: $Π_ℓ A . B$, $sabs(ℓ, A, B, b)$
    / Applications: $sapp(ℓ, A, B, f, a)$
    / Dependent pairs: $Σ_ℓ A . B$, $smk(ℓ, A, B, a, b)$
    / Pair projections: $π_(l A . B) (e)$, $π_(r A . B) (e)$
    / Dependent if-then-else: $site(φ, A, a, b)$
    / Propositional truncations: $||A||$
    / Choice terms: $ε A . φ$
    / Natural numbers: $ℕ$, $0$, $ssucc$
    / Iteration: $natrec(C, n, z, s)$
  ],
  [
    We introduce syntax sugar:
    / Propositions: $bold(2) = cal(U)_0$
    / Booleans: $⊤ := bold(1)_0$, $⊥ := bold(0)_0$
    / Functions: $A → B := Π A . wk0(B)$
    / Negations: $¬A := A → ⊥$
    / Existential quantifiers: $∃A . φ := ||Σ A . φ||$
  ]
)

== Judgements

#align(center, table(
  stroke: none,
  columns: 3,
  row-gutter: 0.5em,
  column-gutter: 3em,
  table.header(
    "Judgement", "Reading", "Definition"
  ),
  $Γ ⊢ a ≡ b : B$, ["In $Γ$, $a$ is equal to $b$ at type $A$"], [Primitive],
  $isok(Γ)$, ["$Γ$ is a well-formed context"], $Γ ⊢ 0 ≡ 0 : ℕ$,
  $Γ ⊢ a : A$, ["In $Γ$, $a$ has type $A$"], $Γ ⊢ a ≡ a : A$,
  $Γ ⊢ A$, ["In $Γ$, $A$ is inhabited"], $∃a . Γ ⊢ a : A$
))

== Rules

#let display-row(..rules) = align(center, stack(
  dir: ltr,
  spacing: 1.5em,
  ..rules.pos().map((rule) => align(horizon, rule))
))

=== Context well-formedness

#display-row(
  prooftree(rule(
    name: [nil-ok],
    $· ⊢ 0 ≡ 0 : ℕ$,
    $$
  )),
  prooftree(rule(
    name: [cons-ok],
    $Γ, x : A ⊢ 0 ≡ 0 : ℕ$,
    $Γ ⊢ 0 ≡ 0 : ℕ$,
    $x ∉ Γ$,
    $Γ ⊢ A : cal(U)_ℓ$,
  ))
)
#display-row(
  prooftree(rule(
    name: $cal(U)$,
    $Γ ⊢ cal(U)_ℓ : cal(U)_(ℓ + 1)$,
    isok($Γ$)
  )),
  prooftree(rule(
    name: [var],
    $Γ ⊢ x : A$,
    isok($Γ$),
    $Γ(x) = A$,
  ))
)

=== Congruence Rules

#display-row(
  prooftree(rule(
    name: $bold(1)$,
    $Γ ⊢ bold(1)_ℓ : cal(U)_ℓ$,
    isok($Γ$)
  )),
  prooftree(rule(
    name: $*$,
    $Γ ⊢ *_ℓ : bold(1)_ℓ$,
    isok($Γ$)
  )),
  prooftree(rule(
    name: $bold(0)$,
    $Γ ⊢ bold(0)_ℓ : cal(U)_ℓ$,
    isok($Γ$),
  )),
  prooftree(rule(
    name: $ℕ$,
    $Γ ⊢ ℕ : cal(U)_1$,
    isok($Γ$)
  )),
  prooftree(rule(
    name: $ssucc$,
    $Γ ⊢ ssucc : ℕ → ℕ$,
    isok($Γ$)
  ))
)

#display-row(
  prooftree(rule(
    name: [eqn],
    $Γ ⊢ (a eqa(A) b) ≡ (a' eqa(A') b') : bold(2)$,
    $Γ ⊢ A ≡ A' : cal(U)_ℓ$,
    $Γ ⊢ a ≡ a' : A$,
    $Γ ⊢ b ≡ b' : A$,
  ))
)

#display-row(
  prooftree(rule(
    name: $Π$,
    $Γ ⊢ Π_(imax(m, n)) A . B ≡ Π_(imax(m, n)) A' . B' : cal(U)_(imax(m, n))$,
    $Γ ⊢ A ≡ A' : cal(U)_m$,
    $Γ, x : A ⊢ B^x ≡ B'^x : cal(U)_n$,
  ))
)

#display-row(
  prooftree(rule(
    name: [app],
    $Γ ⊢ sapp(m ⊔ n, A, B, f, a) ≡ sapp(m ⊔ n, A', B', f', a') : B^a$,
    $Γ ⊢ A ≡ A' : cal(U)_m$,
    $Γ, x : A ⊢ B^x ≡ B'^x : cal(U)_n$,
    $Γ ⊢ f ≡ f' : Π A . B$,
    $Γ ⊢ a ≡ a' : A$,
  ))
)

#display-row(
  prooftree(rule(
    name: $λ$,
    $Γ ⊢ sabs(imax(m, n), A, B, b) ≡ sabs(ℓ, A', B', b') : Π_(imax(m, n)) A . B$,
    $Γ ⊢ A ≡ A' : cal(U)_m$,
    $Γ, x : A ⊢ B^x ≡ B'^x : cal(U)_n$,
    $Γ, x : A ⊢ b^x ≡ b'^x : B^x$
  ))
)

#display-row(
  prooftree(rule(
    name: $Σ$,
    $Γ ⊢ Σ_(m ⊔ n) A . B ≡ Σ_(m ⊔ n) A' . B' : cal(U)_(m ⊔ n)$,
    $Γ ⊢ A ≡ A' : cal(U)_m$,
    $Γ, x : A ⊢ B^x ≡ B'^x : cal(U)_n$,
  ))
)

#display-row(
  prooftree(rule(
    name: [mk],
    $Γ ⊢ smk(ℓ, A, B, a, b) ≡ smk(ℓ, A', B', a', b') : Σ_(m ⊔ n) A . B$,
    $Γ ⊢ A ≡ A' : cal(U)_m$,
    $Γ, x : A ⊢ B^x ≡ B'^x : cal(U)_n$,
    $Γ ⊢ a ≡ a' : A$,
    $Γ ⊢ b ≡ b' : B^a$
  ))
)

#display-row(
  prooftree(rule(
    name: $π_l$,
    $Γ ⊢ π^l_(m ⊔ n . A . B) (e) ≡ π^l_(m ⊔ n .  A' . B') (e') : A$,
    $Γ ⊢ A ≡ A' : cal(U)_m$,
    $Γ, x : A ⊢ B^x ≡ B'^x : cal(U)_n$,
    $Γ ⊢ e ≡ e' : Σ_(m ⊔ n) A . B$,
  ))
)

#display-row(
  prooftree(rule(
    name: $π_r$,
    $Γ ⊢ π^r_(m ⊔ n . A . B) (e) ≡ π_(r A' . B') (e') : B^(π^l_(m ⊔ n . A . B) (e))$,
    $Γ ⊢ A ≡ A' : cal(U)_m$,
    $Γ, x : A ⊢ B^x ≡ B'^x : cal(U)_n$,
    $Γ ⊢ e ≡ e' : Σ_(m ⊔ n) A . B$,
  ))
)

#display-row(
  prooftree(rule(
    name: [dite],
    $Γ ⊢ site(φ, A, a, b) ≡ site(φ', A', a', b') : A$,
    $Γ ⊢ φ ≡ φ' : bold(2)$,
    $Γ ⊢ A ≡ A' : cal(U)_ℓ$,
    $Γ, x : φ ⊢ a ≡ a' : A$,
    $x ∉ tfv(a)$,
    $Γ, y : ¬φ ⊢ b ≡ b' : A$,
    $y ∉ tfv(b)$,
  ))
)

#display-row(
  prooftree(rule(
    name: [tr],
    $Γ ⊢ ||A|| ≡ ||A'|| : bold(2)$,
    $Γ ⊢ A ≡ A' : cal(U)_ℓ$,
  )),
  prooftree(rule(
    name: $ε$,
    $Γ ⊢ ε A . φ ≡ ε A' . φ' : A$,
    $Γ ⊢ A ≡ A' : cal(U)_ℓ$,
    $Γ ⊢ ||A|| ≡ ⊤ : bold(2)$,
    $Γ, x : A ⊢ φ^x ≡ φ'^x : bold(2)$
  ))
)

#display-row(
  prooftree(rule(
    name: $sans("rec")_ℕ$,
    $Γ ⊢ natrec(C, n, z, s) ≡ natrec(C', n', z', s') : C^n$,
    $Γ, x : ℕ ⊢ C^x ≡ C'^x : cal(U)_ℓ$,
    $Γ ⊢ n ≡ n' : ℕ$,
    $Γ ⊢ z ≡ z' : C^0$,
    $Γ, x : ℕ ⊢ s^x ≡ s'^x : C^x → C^(sapp(ℓ, ℕ, ℕ, ssucc, x))$,
  ))
)

=== Equations

#display-row(
  prooftree(rule(
    name: $!_*$,
    $Γ ⊢ a ≡ *_0 : bold(2)$,
    $Γ ⊢ A : bold(2)$,
    $Γ ⊢ a : A$,
  )),
  prooftree(rule(
    name: $⊥_bold(0)$,
    $Γ ⊢ ⊤ ≡ ⊥ : bold(2)$,
    $Γ ⊢ a : bold(0)_ℓ$
  )),
  prooftree(rule(
    name: $⊤_=$,
    $Γ ⊢ (a eqa(A) b) ≡ ⊤ : bold(2)$,
    $Γ ⊢ a ≡ b : A$
  )),
)

#display-row(
  prooftree(rule(
    name: $β$,
    $Γ ⊢ sapp(imax(m, n), A, B, sabs(imax(m, n), A, B, b), a) ≡ b^a : B^a$,
    $Γ ⊢ A : cal(U)_m$,
    $Γ, x : A ⊢ B^x : cal(U)_n$,
    $Γ ⊢ a : A$,
    $Γ, x : A ⊢ b^x : B^x$,
  ))
)

#display-row(
  prooftree(rule(
    name: $β_(π_l)$,
    $Γ ⊢ π^l_(m ⊔ n . A . B) (smk(m ⊔ n, A, B, a, b)) ≡ a : A$,
    $Γ ⊢ A : cal(U)_m$,
    $Γ, x : A ⊢ B^x : cal(U)_n$,
    $Γ ⊢ a : A$,
    $Γ ⊢ b : B^a$
  ))
)

#display-row(
  prooftree(rule(
    name: $β_(π_r)$,
    $Γ ⊢ π^r_(m ⊔ n . A . B) (smk(m ⊔ n, A, B, a, b)) ≡ b : B^a$,
    $Γ ⊢ A : cal(U)_m$,
    $Γ, x : A ⊢ B^x : cal(U)_n$,
    $Γ ⊢ a : A$,
    $Γ ⊢ b : B^a$
  ))
)

#display-row(
  prooftree(rule(
    name: $β_⊤$,
    $Γ ⊢ site(φ, A, a, b) ≡ a : A$,
    $Γ ⊢ φ ≡ ⊤ : bold(2)$,
    $Γ ⊢ A : cal(U)_ℓ$,
    $Γ, x : φ ⊢ a : A$,
    $x ∉ tfv(a)$,
    $Γ, y : ¬φ ⊢ b : A$,
    $y ∉ tfv(b)$,
  ))
)

#display-row(
  prooftree(rule(
    name: $β_⊥$,
    $Γ ⊢ site(φ, A, a, b) ≡ b : A$,
    $Γ ⊢ φ ≡ ⊥ : bold(2)$,
    $Γ ⊢ A : cal(U)_ℓ$,
    $Γ, x : φ ⊢ a : A$,
    $x ∉ tfv(a)$,
    $Γ, y : ¬φ ⊢ b : A$,
    $y ∉ tfv(b)$,
  ))
)

#display-row(
  prooftree(rule(
    name: [$sans("rec")_ℕ$-0],
    $Γ ⊢ natrec(C, 0, z, s) ≡ z : C^0$,
    $Γ, x : ℕ ⊢ C^x : cal(U)_ℓ$,
    $Γ ⊢ z : C^0$,
    $Γ, x : ℕ ⊢ s^x : C^x → C^(sapp(ℓ, ℕ, ℕ, ssucc, x))$,
  ))
)

#display-row(
  prooftree(rule(
    name: [$sans("rec")_ℕ$-$sans("s")$],
    $Γ ⊢ natrec(C, sapp(ℓ, ℕ, ℕ, ssucc, n), z, s) 
        ≡ sapp(ℓ, C^n, C^(sapp(1, ℕ, ℕ, ssucc, n)), s, natrec(C, n, z, s)) 
        : C^(sapp(1, ℕ, ℕ, ssucc, n))$,
    $Γ, x : ℕ ⊢ C^x : cal(U)_ℓ$,
    $Γ ⊢ n : ℕ$,
    $Γ ⊢ z : C^0$,
    $Γ, x : ℕ ⊢ s^x : C^x → C^(sapp(1, ℕ, ℕ, ssucc, x))$,
  ))
)

=== Axioms

#display-row(
  prooftree(rule(
    name: [ext],
    $Γ ⊢ a ≡ b : A$,
    $Γ ⊢ a eqa(A) b$,
  )),
  prooftree(rule(
    name: [propext],
    $Γ ⊢ A ≡ B : bold(2)$,
    $Γ ⊢ A : bold(2)$,
    $Γ ⊢ B : bold(2)$,
    $Γ ⊢ A -> B$,
    $Γ ⊢ B -> A$,
  )),
)

#display-row(
  prooftree(rule(
    name: $"ext"_Σ$,
    $Γ ⊢ smk(m ⊔ n, A, B, π^l_(m ⊔ n . A . B) (e), π^r_(m ⊔ n . A . B) (e)) ≡ e : Σ_(m ⊔ n) A . B$,
    $Γ ⊢ A : cal(U)_m$,
    $Γ, x : A ⊢ B^x : cal(U)_n$,
    $Γ ⊢ e : Σ_(m ⊔ n) A .B$
  ))
)

=== Closure

#display-row(
  prooftree(rule(
    name: [trans],
    $Γ ⊢ a ≡ c : A$,
    $Γ ⊢ a ≡ b : A$,
    $Γ ⊢ b ≡ c : A$,
  )),
  prooftree(rule(
    name: [symm],
    $Γ ⊢ b ≡ a : A$,
    $Γ ⊢ a ≡ b : A$,
  )),
)
#display-row(
  prooftree(rule(
    name: [cast],
    $Γ ⊢ a ≡ b : B$,
    $Γ ⊢ a ≡ b : A$,
    $Γ ⊢ A ≡ B : cal(U)_ℓ$,
  )),
)

#bibliography("references.bib")