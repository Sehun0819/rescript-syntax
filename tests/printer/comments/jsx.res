module Cite = {
  @react.component
  let make = (~author: option<string>, ~children) => {
    // For semantics, check out
    // https://css-tricks.com/quoting-in-html-quotations-citations-and-blockquotes/
    <div>
      foo
    </div>
  }
}

<A
  value=""
  // Comment
/>

<A /* comment */ />

<A>
  // Comment
</A>

<div>
  // Must not jump inside braces
  {React.string("Hello, World!")}
</div>

<div>
  // Must not jump inside braces
  {// But this one is inside
    React.string("Hello, World!")}
</div>

let x = <>
  // before a
  {a} // after a
  // before b
  {b} // after b
</>
