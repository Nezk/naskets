# Naskets

A lazy, purely functional programming language based on the paper *[System F-omega with Equirecursive Types for Datatype-Generic Programming](https://ps.informatik.uni-tuebingen.de/research/functors/equirecursion-fomega-popl16.pdf)* by Yufei Cai, Paolo G. Giarrusso, and Klaus Ostermann.

It's System Fω[^1], with the addition of `μ` and the definitional equality `μ F ≡ F (μ F)`, which is implemented in the [Eval](https://github.com/Nezk/naskets/blob/main/src/Eval.hs) module and described there in detail (about restriction of `μ` on `* → *` and so on), and propositional equality `x ~[κ] y`, where `x, y ∷ κ` (so, it's perfectly possible to express GADTs).

Because of equirecursive types, cute things such as this are expressible:
```
y : forall a :: *. (a -> a) -> a
y = /\a. \f.
  let w = \x : mu (\r :: *. r -> a). f (x x) in
  w w
```
(one shouldn't use it instead of built-in `fix` though due to efficiency reasons)

The language supports top-level evaluation via the `>>` syntax. It functions similarly to `#eval` in Lean or `Eval cbn in …` in Coq, evaluating pure expressions without executing IO side-effects. 

Naskets supports Agda/Idris/etc-style typed holes, using the `?hole` syntax. This pauses the typechecker and prints the local context and the expected goal type. You can also use the `?hole{exp}` syntax to check the `exp` against a goal.

Evaluation is call-by-need (lazy). The interpreter includes cycle detection to explicitly catch and report non-productive, simple infinite loops (similar to Haskell's `<<loop>>` exception (or GHC's — I don't know if it's standardised)).

The provided `Makefile` wraps Cabal: `make` builds and copies the binary to the project root, `make test` runs all the examples.

## Language Reference

### Kinds

| Syntax | Description |
| :--- | :--- |
| `*` | Base kind |
| `κ → κ′` | Arrow kind |

### Types

| Syntax | Description |
| :--- | :--- |
| `Int`, `Double`, `String` | Base types |
| `IO τ` | IO monad |
| `τ → τ′` | Function type |
| `{ l₁ : τ₁, … }` | Record type; `{}` is the unit type (= empty product) |
| `⟨ l₁ : τ₁, … ⟩` | Variant type; `⟨⟩` is the empty variant (void) |
| `∀a ∷ κ. τ` | Universal quantification |
| `∃a ∷ κ. τ` | Existential quantification |
| `μ τ` | Equirecursive type (where `τ ∷ * → *`) |
| `λa ∷ κ. τ` | Type-level lambda; kind annotation is optional |
| `τ σ` | Type application |
| `τ ~[κ] τ′` | Propositional equality at kind `κ` |

*Record and variant labels are sorted canonically (alphabetically) during parsing.*

*Therefore, `{ b : Int, a : String }` and `{ a : String, b : Int }` denote the exact same type.*

### Terms

| Syntax | Description |
| :--- | :--- |
| `λx : τ. e` | Lambda; type annotation is optional |
| `Λa ∷ κ. e` | Type abstraction; kind annotation is optional |
| `e e′` | Term application |
| `e [τ]` | Type application |
| `let x : τ = e in e′` | Let binding; type annotation is optional |
| `{ l₁ = e₁, … }` | Record construction |
| `e.l` | Record projection |
| `⟨ l = e ⟩` | Variant construction |
| `e ? ⟨ l₁ x ↦ e₁ \| … ⟩`| Pattern matching on variants |
| `pack [τ] e` | Existential introduction |
| `unpack e as ⟨a, x⟩ in e′` | Existential elimination |
| `fix e` | Fixed-point combinator |
| `return e` | IO monad lift |
| `e >>= e′` | IO monad bind |
| `42`, `3.14`, `"hello"` | Integer, double, and string literals |
| `(e : τ)` | Type annotation |
| `?h` or `?h{e}` | Typed hole (optionally containing a guess expression `e`) |

### Built-ins

| Syntax | Type |
| :--- | :--- |
| `(+)`, `(-)`, `(*)` | `Int → Int → Int` |
| `(+.)`, `(-.)`, `(*.)` | `Double → Double → Double` |
| `(/.)` | `Double → Double → ⟨ None : {}, Some : Double ⟩` |
| `trunc` | `Double → Int` |
| `(==)` | `Int → Int → ⟨ False : {}, True : {} ⟩` |
| `(=.)` | `Double → Double → ⟨ False : {}, True : {} ⟩` |
| `(=^)` | `String → String → ⟨ False : {}, True : {} ⟩` |
| `(^)` | `String → String → String` |
| `length` | `String → Int` |
| `substring` | `Int → Int → String → String` |
| `showInt` | `Int → String` |
| `showDouble` | `Double → String` |
| `putStr` | `String → IO {}` |
| `getLine` | `IO ⟨ None : {}, Some : String ⟩` |
| `readFile` | `String → IO ⟨ None : {}, Some : String ⟩` |
| `writeFile` | `String → String → IO ⟨ None : {}, Some : {} ⟩` |
| `argCount` | `IO Int` |
| `argAt` | `Int → IO ⟨ None : {}, Some : String ⟩` |
| `refl [κ]` | `∀a ∷ κ. a ~[κ] a` |
| `subst [κ]` | `∀a b ∷ κ. ∀p ∷ κ → *. a ~[κ] b → p a → p b` |

[^1]: This is a genuine implementation of System Fω, unlike the popular educational-ish implementation on GitHub (<https://github.com/sdiehl/typechecker-zoo/>). That repository claims to implement System Fω and even mentions type-level lambdas in its notes' grammar of System Fω, only to completely omit them in the actual code. Without type-level computation, a system is not System Fω. The repository notes excuse this by stating, *"our implementation focuses on the essential features needed for practical programming language design,"* OK, fine, but don’t call it a System Fω then. There also more funny pearls, it claims: *Core types [of this implementation] include all the expressive power of System Fω: <…> Type Abstraction: `TAbs` for creating type-level functions*, i. e., a `Λ` which is not a type-level lambda. `TAbs` appears in the System F implementation (`Expr::TAbs(String, Box<Expr>)`), described there as *"Type Abstraction (Λα.e): This creates a polymorphic function."*, but the System Fω implementation uses `CoreTerm::TypeLambda` with same semantics, but different (misleading) name. Furthermore, the implementation explicitly states it is based on the paper *A Mechanical Formalization of Higher-Ranked Polymorphic Type Inference*. A type system with higher-rank polymorphism **only** is not System Fω. One might generously assume the `-` in their `System F-ω` refers to System Fω⁻ (a restricted subset, that's how sometimes Haskell's typesystem is described), but their notes plainly state `System Fω`. Why one would wish to mislead people is beyond me… Apologies for the grumbling.
